-- Prove2me | solution 1 for OAI.Coulomb.exists_atomic_near_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:29:17.775888+00:00
-- url     : https://prove2.me/submissions/accbcde1-7c15-4712-b970-6d014f602d64

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationSmallScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma tendsto_positive_rpow_zero {q : ℝ} (hq : 0<q) :
    Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow hq.ne'] using
    ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds

lemma screenMass_small_offset {D r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hD : 0 ≤ D) (hsmall : D*r^7 ≤ 1) :
    Coulomb.screenMass D r ≤ 2/r^3 := by
  have hr3 : 0 < r^3 := pow_pos hr _
  have hb : Coulomb.screenBaseMass r=(r^3)⁻¹ := by
    unfold Coulomb.screenBaseMass
    apply max_eq_left
    exact (one_le_inv₀ hr3).mpr (pow_le_one₀ hr.le hr1)
  have hs : Real.sqrt (D*r) ≤ (r^3)⁻¹ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hr3.le)).mp
    rw [Real.sq_sqrt (mul_nonneg hD hr.le), inv_pow, inv_eq_one_div,
      le_div_iff₀ (pow_pos hr3 _)]
    nlinarith [hsmall]
  unfold Coulomb.screenMass
  rw [hb]
  calc
    (r^3)⁻¹+Real.sqrt (D*r) ≤ (r^3)⁻¹+(r^3)⁻¹ := add_le_add le_rfl hs
    _ = 2/r^3 := by ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

lemma FermionicCoefficients.vanish_of_repeat {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    {b : Fin n → α} {i j : Fin n} (hij : i ≠ j) (hb : b i = b j) : f b = 0 := by
  classical
  have heq : b ∘ Equiv.swap i j = b := by
    funext k
    by_cases hi : k = i
    · subst k; simpa using hb.symm
    by_cases hj : k = j
    · subst k; simpa using hb
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  have h := hf (Equiv.swap i j) b
  rw [heq, Equiv.Perm.sign_swap hij] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  have hz : 2 * f b = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

lemma FermionicCoefficients.pointwise_occupation {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f) (a : α) (b : Fin n → α) :
    (∑ i, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ‖f b‖^2 := by
  classical
  by_cases hz : f b = 0
  · simp [hz]
  have hinj : Function.Injective b := by
    intro i j heq
    by_contra hne
    exact hz (hf.vanish_of_repeat hne heq)
  by_cases he : ∃ i, b i = a
  · obtain ⟨i, hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : b j ≠ a := by intro h; exact hji (hinj (h.trans hi.symm))
      simp [hj]
    · simp
  · simp only [not_exists] at he
    simp only [ite_eq_right (he _), Finset.sum_const_zero]
    positivity

lemma FermionicCoefficients.occupation_sum {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (hs : Summable (fun b => ‖f b‖^2)) (a : α) :
    (∑' b, ∑ i, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ∑' b, ‖f b‖^2 := by
  apply Summable.tsum_le_tsum (fun b => hf.pointwise_occupation a b) _ hs
  exact Summable.of_nonneg_of_le (fun b => Finset.sum_nonneg (fun i _ => by positivity))
    (fun b => hf.pointwise_occupation a b) hs

lemma FermionicCoefficients.norm_permute {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (p : Equiv.Perm (Fin n)) (b : Fin n → α) : ‖f (b ∘ p)‖ = ‖f b‖ := by
  rw [hf p b, norm_mul]
  have hsign : ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]
  rw [hsign, one_mul]

lemma FermionicCoefficients.occupation_eq {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (a : α) (i j : Fin n) :
    (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) =
      ∑' b, if b j = a then ‖f b‖^2 else (0 : ℝ) := by
  classical
  let p := Equiv.swap i j
  have he := (coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => if b i = a then ‖f b‖^2 else (0 : ℝ))
  change (∑' b, if (b ∘ p) i = a then ‖f (b ∘ p)‖^2 else (0 : ℝ)) = _ at he
  simp only [Function.comp_apply, p, Equiv.swap_apply_left, hf.norm_permute] at he
  exact he.symm

theorem FermionicCoefficients.pauli_bound {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (hs : Summable (fun b => ‖f b‖^2)) (a : α) (i : Fin n) :
    (n : ℝ) * (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) ≤ ∑' b, ‖f b‖^2 := by
  classical
  have hsi : ∀ j : Fin n, Summable (fun b => if b j = a then ‖f b‖^2 else (0 : ℝ)) := by
    intro j
    exact Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> simp) hs
  have heq : (∑' b, ∑ j : Fin n, if b j = a then ‖f b‖^2 else (0 : ℝ)) =
      (n : ℝ) * (∑' b, if b i = a then ‖f b‖^2 else (0 : ℝ)) := by
    rw [Summable.tsum_finsetSum (fun j _ => hsi j)]
    simp_rw [hf.occupation_eq a _ i]
    simp
  rw [← heq]
  exact hf.occupation_sum hs a

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ConfigurationMeasurableEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

open scoped Classical

theorem HilbertBasis_completeOrbitals {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} (v : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    CompleteOrbitals μ (fun i => v i) := by
  intro f hf hz
  have he : v.repr (hf.toLp f) = 0 := by
    apply lp.ext
    funext i
    rw [v.repr_apply_apply]
    change inner ℂ (v i) (hf.toLp f) = 0
    have hi := inner_toLp_complex (Lp.memLp (v i)) hf
    simp only [Lp.toLp_coeFn] at hi
    rw [hi, hz i]
  have hf0 : hf.toLp f = 0 := v.repr.injective (by simpa using he)
  exact hf.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).1 hf0)

theorem orthonormal_subtype_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [SecondCountableTopology E] {s : Set E}
    (hs : Orthonormal ℂ (Subtype.val : s → E)) : Countable s := by
  have : DiscreteTopology s := DiscreteTopology.of_forall_le_dist (r := 1) (by norm_num) (by
    intro x y hxy
    have he : ‖(x : E) - y‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hs.1 x, hs.1 y, hs.inner_eq_zero hxy]
      norm_num
    change 1 ≤ dist (x : E) (y : E)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg ((x : E) - y)])
  exact countable_of_Lindelof_of_discrete

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma scalarCoefficient_antisymmetric {n : ℕ} {f : (Fin n → A) → ℂ}
    (hf : ProductAntisymmetric (μ := μ) f) (v : ι → A → ℂ) :
    FermionicCoefficients (scalarCoefficient (μ := μ) f v) := by
  intro p b
  unfold scalarCoefficient
  have hp := measurePreserving_piCongrLeft (fun _ : Fin n => μ) p.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ => A) p.symm :
      (Fin n → A) → (Fin n → A)) = fun x => x ∘ p := by
    funext x i
    simpa only [Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => A) p.symm x (p i))
  rw [← hp.integral_comp' (fun x => star (∏ i, v ((b ∘ p) i) (x i)) * f x), he,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hf p] with x hx
  simp only [Function.comp_apply, hx]
  rw [Equiv.prod_comp p (fun i => v (b i) (x i))]
  ring

theorem scalarCoefficient_parseval [Countable ι] {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) :
    (∑' b : Fin n → ι, ‖scalarCoefficient (μ := μ) f v b‖^2) =
      ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have ht := completeOrbitals_parseval (μ := Measure.pi fun _ : Fin n => μ)
    (fun (b : Fin n → ι) (x : Fin n → A) => ∏ i, v (b i) (x i))
    (scalarTensor_memLp v hv) (by
      intro b c
      have h := scalarTensor_orthonormal (μ := μ) v ho b c
      by_cases he : b = c <;> simpa only [he, ite_true, ite_false] using h)
    (completeOrbitals_finPi v hv hc n) f hf
  simpa only [scalarCoefficient] using ht

lemma scalarCoefficient_summable {n : ℕ}
    (f : (Fin n → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    Summable (fun b : Fin n → ι => ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  have ho' : Orthonormal ℂ (fun b : Fin n → ι =>
      (scalarTensor_memLp v hv b).toLp (fun x : Fin n → A => ∏ i, v (b i) (x i))) := by
    rw [orthonormal_iff_ite]
    intro b c
    rw [inner_toLp_complex]
    exact scalarTensor_orthonormal v ho b c
  have hs := ho'.inner_products_summable (hf.toLp f)
  simpa only [inner_toLp_complex, scalarCoefficient] using hs

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinMode
attribute [-instance] _root_.OAI.Coulomb.spinCubeMeasure_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma spinDelta_memLp (s : Fin 2) : MemLp (spinDelta s) 2 Measure.count := by
  apply MemLp.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun t => by simp [spinDelta]; split_ifs <;> norm_num)

lemma spinDelta_inner (s t : Fin 2) :
    (∫ q, star (spinDelta s q) * spinDelta t q ∂Measure.count) =
      if s = t then (1 : ℂ) else 0 := by
  classical
  simp [integral_count, spinDelta, eq_comm]

lemma spinDelta_complete : CompleteOrbitals Measure.count spinDelta := by
  intro f _ hz
  apply ae_of_all
  intro s
  have H := hz s
  simpa [integral_count, spinDelta] using H

lemma cubeMode_memLp (b : ℝ) {d : ℕ} (q : Fin d → ℕ) :
    MemLp (cubeMode b q) 2 (cubeMeasure b d) :=
  scalarTensor_memLp (neumannMode b) (neumannMode_memLp b) q

lemma spinCubeMode_memLp (b : ℝ) (a : SpinMode) :
    MemLp (spinCubeMode b a) 2 (spinCubeMeasure b) :=
  tensorPair_memLp (spinDelta_memLp a.1) (cubeMode_memLp b a.2)

lemma spinCubeMode_complete {b : ℝ} (hb : 0 < b) :
    CompleteOrbitals (spinCubeMeasure b) (spinCubeMode b) :=
  completeOrbitals_tensorPair (fun q => cubeMode_memLp b q) spinDelta_memLp
    (cubeMode_complete hb 3) spinDelta_complete

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_HilbertBasisContaining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma exists_hilbertBasis_containing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (v : E) (hv : ‖v‖ = 1) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (i : w), b i = v ∧ ⇑b = Subtype.val := by
  have ho : Orthonormal ℂ ((↑) : ({v} : Set E) → E) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : E) = v := Set.mem_singleton_iff.mp i.property
    have hj : (j : E) = v := Set.mem_singleton_iff.mp j.property
    have he : i = j := Subtype.ext (hi.trans hj.symm)
    simp [he, hj, inner_self_eq_norm_sq_to_K, hv]
  obtain ⟨w, b, hw, hb⟩ := ho.exists_hilbertBasis_extension
  exact ⟨w, b, ⟨v, hw (Set.mem_singleton v)⟩, congrFun hb _, hb⟩

lemma scalarCoefficient_contract {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) (a : ι) (b : Fin n → ι) :
    scalarCoefficient (μ := μ) f v (Fin.cons a b) =
      scalarCoefficient (μ := μ)
        (fiberContract (μ := μ) (v a) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1))) v b := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans (Measure.measurePreserving_swap)
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  have hf' : MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
    simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)
  unfold scalarCoefficient
  rw [← (he.symm e).integral_comp']
  simp only [hcons]
  have hprod (z : (Fin n → A) × A) :
      (∏ i : Fin (n+1), v ((Fin.cons a b : Fin (n+1) → ι) i)
        ((Fin.cons z.2 z.1 : Fin (n+1) → A) i)) =
        (∏ i : Fin n, v (b i) (z.1 i)) * v a z.2 := by
    rw [Fin.prod_univ_succ]
    simp [mul_comm]
  simp only [hprod]
  exact integral_tensorPair (scalarTensor_memLp v hv b) (hv a) hf'

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TsumFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma tsum_fixed_zero {ι : Type*} {n : ℕ} (f : (Fin (n+1) → ι) → ℝ) (a : ι) :
    (∑' b : Fin (n+1) → ι, if b 0 = a then f b else 0) =
      ∑' c : Fin n → ι, f (Fin.cons a c) := by
  have hinj : Function.Injective (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro c d h
    funext i
    exact congrFun h i.succ
  have hs : Function.support (fun b : Fin (n+1) → ι => if b 0 = a then f b else 0) ⊆
      Set.range (fun c : Fin n → ι => (Fin.cons a c : Fin (n+1) → ι)) := by
    intro b hb
    have ha : b 0 = a := by
      by_contra hh
      exact hb (ite_eq_right hh)
    exact ⟨Fin.tail b, by simpa only [← ha] using Fin.cons_self_tail b⟩
  simpa only [Fin.cons_zero, ite_true] using (hinj.tsum_eq hs).symm

lemma basis_contraction_pauli {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (a : ι) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) (v a) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤ ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have hp := (scalarCoefficient_antisymmetric ha v).pauli_bound
    (scalarCoefficient_summable f hf v hv ho) a 0
  rw [scalarCoefficient_parseval f hf v hv ho hc, tsum_fixed_zero] at hp
  simp only [scalarCoefficient_contract f hf v hv] at hp
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  have hf' : MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
    simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)
  rw [scalarCoefficient_parseval _ (fiberContract_memLp (hv a) hf') v hv ho hc] at hp
  exact hp

lemma unit_contraction_pauli {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : A → ℂ) (hv : MemLp v 2 μ) (hv1 : ∫ x, ‖v x‖^2 ∂μ = 1) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤ ∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ) := by
  have hn : ‖hv.toLp v‖ = 1 := by
    have hs := norm_toLp_sq_complex hv
    rw [hv1] at hs
    nlinarith [norm_nonneg (hv.toLp v)]
  obtain ⟨w, b, i, hbi, hb⟩ := exists_hilbertBasis_containing (hv.toLp v) hn
  have : Countable w := orthonormal_subtype_countable (by
    simpa only [hb] using b.orthonormal)
  have ho (j k : w) : (∫ a, star (b j a) * b k a ∂μ) = if j = k then (1:ℂ) else 0 := by
    rw [← inner_toLp_complex (Lp.memLp (b j)) (Lp.memLp (b k))]
    simp only [Lp.toLp_coeFn]
    exact (orthonormal_iff_ite.mp b.orthonormal) j k
  have H := basis_contraction_pauli f hf ha (fun j => b j) (fun j => Lp.memLp (b j))
    (by intro j k; by_cases h : j = k <;>
      simpa only [h, ite_true, ite_false] using ho j k) (HilbertBasis_completeOrbitals b) i
  have he : (fun a => b i a) =ᵐ[μ] v := by
    simpa only [hbi] using hv.coeFn_toLp
  have hc (y : Fin n → A) :
      fiberContract (μ := μ) (b i) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y =
      fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y := by
    unfold fiberContract
    apply integral_congr_ae
    filter_upwards [he] with a ha
    rw [ha]
  simpa only [hc] using H

lemma fiberContract_const_mul {A B : Type*} [MeasurableSpace A] {μ : Measure A}
    (c : ℂ) (v : A → ℂ) (f : B × A → ℂ) (y : B) :
    fiberContract (μ := μ) (fun x => c * v x) f y = star c * fiberContract (μ := μ) v f y := by
  unfold fiberContract
  rw [show (fun a => star (c * v a) * f (y,a)) =
    (fun a => star c * (star (v a) * f (y,a))) from by
      funext a; simp only [star_mul]; ring, integral_const_mul]

lemma contraction_pauli {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f) (v : A → ℂ) (hv : MemLp v 2 μ) :
    ((n+1 : ℕ) : ℝ) * (∫ y : Fin n → A,
      ‖fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2
        ∂(Measure.pi fun _ => μ)) ≤
      (∫ x, ‖v x‖^2 ∂μ) * (∫ x, ‖f x‖^2 ∂(Measure.pi fun _ => μ)) := by
  let t : ℝ := ‖hv.toLp v‖
  have ht : 0 ≤ t := norm_nonneg _
  have ht2 : t^2 = ∫ x, ‖v x‖^2 ∂μ := norm_toLp_sq_complex hv
  by_cases hz : t = 0
  · have hv0 : hv.toLp v = 0 := norm_eq_zero.mp hz
    have hev : v =ᵐ[μ] 0 := hv.coeFn_toLp.symm.trans ((Lp.eq_zero_iff_ae_eq_zero).mp hv0)
    have hc (y : Fin n → A) :
        fiberContract (μ := μ) v (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y = 0 := by
      unfold fiberContract
      apply integral_eq_zero_of_ae
      filter_upwards [hev] with x hx
      simp [hx]
    simp only [← ht2, hz, zero_pow (by decide : 2 ≠ 0), zero_mul, hc, norm_zero, integral_zero,
      mul_zero, le_refl]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    let u : A → ℂ := fun x => (t⁻¹ : ℂ) * v x
    have hu : MemLp u 2 μ := hv.const_mul _
    have hu1 : (∫ x, ‖u x‖^2 ∂μ) = 1 := by
      simp only [u, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
        mul_pow, integral_const_mul, ← ht2]
      field_simp
    have H := unit_contraction_pauli f hf ha u hu hu1
    simp only [u, fiberContract_const_mul, norm_mul, norm_star, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, mul_pow, integral_const_mul] at H
    rw [← ht2]
    have H' := mul_le_mul_of_nonneg_left H (sq_nonneg t)
    have he : t^2 * (((n+1:ℕ):ℝ) * ((t⁻¹)^2 *
        (∫ y : Fin n → A, ‖fiberContract (μ := μ) v
          (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2 ∂(Measure.pi fun _ => μ)))) =
        ((n+1:ℕ):ℝ) * (∫ y : Fin n → A, ‖fiberContract (μ := μ) v
          (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) y‖^2 ∂(Measure.pi fun _ => μ)) := by
      field_simp
    rwa [he] at H'

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include ho in
lemma orbital_orthonormal : Orthonormal ℂ (fun i => (hv i).toLp (v i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_toLp_complex]
  exact ho i j

lemma orbital_sum_toLp (s : Finset ι) (c : ι → ℂ) :
    (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) =
      ∑ i ∈ s, c i • (hv i).toLp (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    have he : (fun x => ∑ i ∈ insert a s, c i * v i x) =
        (fun x => c a * v a x) + (fun x => ∑ i ∈ s, c i * v i x) := by
      funext x
      simp [Finset.sum_insert ha]
    rw [show (orbital_sum_memLp v hv (insert a s) c).toLp _ =
      ((hv a).const_mul (c a)).toLp (fun x => c a * v a x) +
      (orbital_sum_memLp v hv s c).toLp (fun x => ∑ i ∈ s, c i * v i x) from by
        simpa only [he] using ((hv a).const_mul (c a)).toLp_add
          (orbital_sum_memLp v hv s c)]
    rw [ih, Finset.sum_insert ha]
    congr 1

include hv ho in
lemma orbital_sum_sq (s : Finset ι) (c : ι → ℂ) :
    (∫ x, ‖∑ i ∈ s, c i * v i x‖^2 ∂μ) = ∑ i ∈ s, ‖c i‖^2 := by
  rw [← norm_toLp_sq_complex (orbital_sum_memLp v hv s c), orbital_sum_toLp v hv s c]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ i ∈ s, c i • (hv i).toLp (v i)‖^2) : ℂ) =
        inner ℂ (∑ i ∈ s, c i • (hv i).toLp (v i))
          (∑ i ∈ s, c i • (hv i).toLp (v i)) := by
      simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    _ = ∑ i ∈ s, star (c i) * c i := (orbital_orthonormal v hv ho).inner_sum c c s
    _ = ∑ i ∈ s, (↑(‖c i‖^2) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [starRingEnd_apply, Complex.ofReal_pow] using Complex.conj_mul' (c i)

include hv in
lemma lowOrbital_memLp (s : Finset ι) (x : A) :
    MemLp (lowOrbital v s x) 2 μ := orbital_sum_memLp v hv s _

include hv ho in
lemma lowOrbital_sq (s : Finset ι) (x : A) :
    (∫ y, ‖lowOrbital v s x y‖^2 ∂μ) = ∑ i ∈ s, ‖v i x‖^2 := by
  simpa only [lowOrbital, norm_star] using orbital_sum_sq v hv ho s (fun i => star (v i x))

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_LowProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
section LowProjection
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)

include hv in
lemma lowProjection_memLp (s : Finset ι) {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (lowProjection (μ := μ) v s f) 2 (ν.prod μ) :=
  memLp_finsetSum s (fun i _ => tensorPair_memLp (fiberContract_memLp (hv i) hf) (hv i))

include hv in
lemma lowProjection_tail_memLp (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (x : A) :
    MemLp (fun y => lowProjection (μ := μ) v s f (y,x)) 2 ν :=
  memLp_finsetSum s (fun i _ => (fiberContract_memLp (hv i) hf).mul_const (v i x))

include hv in
lemma lowProjection_eq_contract (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (x : A) :
    (fun y => lowProjection (μ := μ) v s f (y,x)) =ᵐ[ν]
      fiberContract (μ := μ) (lowOrbital v s x) f := by
  filter_upwards [memLp_fiber_ae hf] with y hy
  unfold lowProjection fiberContract lowOrbital
  rw [show (fun a => star (∑ i ∈ s, star (v i x) * v i a) * f (y,a)) =
      (fun a => ∑ i ∈ s, (star (v i a) * f (y,a)) * v i x) from by
    funext a
    simp only [star_sum, star_mul, star_star, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [integral_finsetSum s (fun i _ => (integrable_star_mul (hv i) hy).mul_const (v i x))]
  simp only [integral_mul_const]

end LowProjection
end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_FirstFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma firstFiber_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ} (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    MemLp (firstFiber f) 2 ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  change MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2 _
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)

lemma lowProjection_density_pauli {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (s : Finset ι) (x : A) :
    ((n+1:ℕ):ℝ) * (∫ y : Fin n → A, ‖lowProjection (μ := μ) v s (firstFiber f) (y,x)‖^2
      ∂(Measure.pi fun _ => μ)) ≤
      (∑ i ∈ s, ‖v i x‖^2) * (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) := by
  have H := contraction_pauli f hf ha (lowOrbital v s x) (lowOrbital_memLp v hv s x)
  rw [lowOrbital_sq v hv ho] at H
  have he := lowProjection_eq_contract v hv s (firstFiber_memLp hf) x
  have he' : (∫ y : Fin n → A, ‖lowProjection (μ := μ) v s (firstFiber f) (y,x)‖^2
      ∂(Measure.pi fun _ => μ)) =
      ∫ y : Fin n → A, ‖fiberContract (μ := μ) (lowOrbital v s x) (firstFiber f) y‖^2
        ∂(Measure.pi fun _ => μ) := integral_congr_ae (he.fun_comp fun z => ‖z‖^2)
  rw [he']
  exact H

lemma norm_sq_le_two_norm_sq_add_sub (a b : ℂ) :
    ‖a‖^2 ≤ 2*‖b‖^2 + 2*‖a-b‖^2 := by
  have h : ‖a‖ ≤ ‖b‖ + ‖a-b‖ := by
    simpa only [add_sub_cancel] using norm_add_le b (a-b)
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a-b), sq_nonneg (‖b‖-‖a-b‖)]

lemma fiber_norm_sq_split {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f g : A → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, ‖f x‖^2 ∂μ) ≤ 2*(∫ x, ‖g x‖^2 ∂μ) + 2*(∫ x, ‖f x-g x‖^2 ∂μ) := by
  have hi : Integrable (fun x => ‖f x-g x‖^2) μ := (hf.sub hg).norm.integrable_sq
  calc
    _ ≤ ∫ x, 2*‖g x‖^2 + 2*‖f x-g x‖^2 ∂μ :=
      integral_mono hf.norm.integrable_sq
        ((hg.norm.integrable_sq.const_mul 2).add (hi.const_mul 2))
        (fun x => norm_sq_le_two_norm_sq_add_sub (f x) (g x))
    _ = _ := by rw [integral_add (hg.norm.integrable_sq.const_mul 2)
        (hi.const_mul 2), integral_const_mul, integral_const_mul]

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_HighProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

section
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

omit [MeasurableSpace B] [SigmaFinite μ] in
include hv ho in
lemma fiberContract_lowProjection (s : Finset ι) (f : B × A → ℂ) (a : ι) (y : B) :
    fiberContract (μ := μ) (v a) (lowProjection (μ := μ) v s f) y =
      if a ∈ s then fiberContract (μ := μ) (v a) f y else 0 := by
  classical
  dsimp only [lowProjection, fiberContract]
  rw [show (fun x => star (v a x) * ∑ i ∈ s,
        (∫ z, star (v i z) * f (y,z) ∂μ) * v i x) =
      (fun x => ∑ i ∈ s, (∫ z, star (v i z) * f (y,z) ∂μ) * (star (v a x) * v i x)) from by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [integral_finsetSum s (fun i _ => (integrable_star_mul (hv a) (hv i)).const_mul _)]
  simp only [integral_const_mul, ho, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

include hv in
lemma highProjection_memLp (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (highProjection (μ := μ) v s f) 2 (ν.prod μ) := by
  have hp : MemLp (lowProjection (μ := μ) v s f) 2 (ν.prod μ) :=
    lowProjection_memLp v hv s hf
  change MemLp (f - lowProjection (μ := μ) v s f) 2 (ν.prod μ)
  exact hf.sub hp

include hv ho in
lemma fiberContract_highProjection (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (a : ι) :
    fiberContract (μ := μ) (v a) (highProjection (μ := μ) v s f) =ᵐ[ν]
      fun y => if a ∈ s then 0 else fiberContract (μ := μ) (v a) f y := by
  classical
  filter_upwards [memLp_fiber_ae hf] with y hy
  have hp : MemLp (fun x => lowProjection (μ := μ) v s f (y,x)) 2 μ :=
    orbital_sum_memLp v hv s (fun i => fiberContract (μ := μ) (v i) f y)
  change (∫ x, star (v a x) * (f (y,x) - lowProjection (μ := μ) v s f (y,x)) ∂μ) = _
  simp only [mul_sub]
  rw [integral_sub (integrable_star_mul (hv a) hy) (integrable_star_mul (hv a) hp)]
  change fiberContract (μ := μ) (v a) f y -
    fiberContract (μ := μ) (v a) (lowProjection (μ := μ) v s f) y = _
  rw [fiberContract_lowProjection v hv ho]
  split_ifs <;> simp only [sub_self, sub_zero]

end

lemma firstFiber_firstUnfiber {A : Type*} {n : ℕ} (f : (Fin n → A) × A → ℂ) :
    firstFiber (firstUnfiber f) = f := by
  funext z
  simp only [firstFiber, firstUnfiber, Fin.tail_cons, Fin.cons_zero]

lemma firstUnfiber_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} {f : (Fin n → A) × A → ℂ}
    (hf : MemLp f 2 ((Measure.pi fun _ : Fin n => μ).prod μ)) :
    MemLp (firstUnfiber f) 2 (Measure.pi fun _ => μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  have heq : ∀ x : Fin (n+1) → A, e x = (Fin.tail x, x 0) := by
    intro x
    rfl
  change MemLp (fun x : Fin (n+1) → A => f (Fin.tail x, x 0)) 2 (Measure.pi fun _ => μ)
  simpa only [Function.comp_def, heq] using hf.comp_measurePreserving he

lemma firstUnfiber_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    {n : ℕ} (f : (Fin n → A) × A → ℂ) :
    (∫ x, ‖firstUnfiber f x‖^2 ∂(Measure.pi fun _ => μ)) =
      ∫ z, ‖f z‖^2 ∂((Measure.pi fun _ : Fin n => μ).prod μ) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans Measure.measurePreserving_swap
  exact he.integral_comp' (fun z => ‖f z‖^2)

lemma scalarCoefficient_congr {A ι : Type*} [MeasurableSpace A] {μ : Measure A}
    {n : ℕ} {f g : (Fin n → A) → ℂ} (he : f =ᵐ[Measure.pi fun _ => μ] g)
    (v : ι → A → ℂ) (b : Fin n → ι) :
    scalarCoefficient (μ := μ) f v b = scalarCoefficient (μ := μ) g v b := by
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)

include hv ho in
lemma scalarCoefficient_highFirst {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (s : Finset ι) (b : Fin (n+1) → ι) :
    scalarCoefficient (μ := μ) (firstUnfiber (highProjection (μ := μ) v s (firstFiber f))) v b =
      if b 0 ∈ s then 0 else scalarCoefficient (μ := μ) f v b := by
  classical
  have hff := firstFiber_memLp hf
  have hh := highProjection_memLp v hv s hff
  have hu := firstUnfiber_memLp hh
  have hb : Fin.cons (b 0) (Fin.tail b) = b := by
    ext i
    exact Fin.cases rfl (fun j => rfl) i
  rw [← hb, scalarCoefficient_contract _ hu v hv, scalarCoefficient_contract f hf v hv]
  change scalarCoefficient (μ := μ)
    (fiberContract (μ := μ) (v (b 0)) (firstFiber (firstUnfiber
      (highProjection (μ := μ) v s (firstFiber f))))) v (Fin.tail b) = _
  rw [firstFiber_firstUnfiber]
  rw [scalarCoefficient_congr (fiberContract_highProjection v hv ho s hff (b 0))]
  by_cases hs : b 0 ∈ s
  · simp only [Fin.cons_zero, hs, ite_true, scalarCoefficient, mul_zero, integral_zero]
  · simp only [Fin.cons_zero, hs, ite_false]
    rfl

include hv ho in
lemma highProjection_norm_spectrum [Countable ι] (hc : CompleteOrbitals μ v)
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (s : Finset ι) :
    (∫ z, ‖highProjection (μ := μ) v s (firstFiber f) z‖^2
      ∂((Measure.pi fun _ : Fin n => μ).prod μ)) =
      ∑' b, if b 0 ∈ s then 0 else ‖scalarCoefficient (μ := μ) f v b‖^2 := by
  rw [← firstUnfiber_norm_sq]
  have hh := highProjection_memLp v hv s (firstFiber_memLp hf)
  rw [← scalarCoefficient_parseval _ (firstUnfiber_memLp hh) v hv ho hc]
  apply tsum_congr
  intro b
  rw [scalarCoefficient_highFirst v hv ho hf s b]
  split_ifs <;> norm_num

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DyadicTailPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma dyadic_tail_partial_le {w : ℝ} (hw : 0 ≤ w) (N : ℕ) :
    (∑ k ∈ Finset.range N, if (4:ℝ)^k < w then (4:ℝ)^k else 0) ≤ (4/3:ℝ)*w := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ N ih =>
    by_cases h : (4:ℝ)^N < w
    · calc
        _ ≤ ∑ k ∈ Finset.range (N+1), (4:ℝ)^k := by
          apply Finset.sum_le_sum
          intro k _
          split_ifs
          · exact le_rfl
          · positivity
        _ = ((4:ℝ)^(N+1)-1)/3 := by rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1)]; norm_num
        _ ≤ (4/3:ℝ)*w := by rw [pow_succ]; linarith
    · simpa only [Finset.sum_range_succ, ite_eq_right h, add_zero] using ih

lemma dyadic_tail_hasSum {w : ℝ} (hw : 0 ≤ w) :
    Summable (fun k : ℕ => if (4:ℝ)^k < w then (4:ℝ)^k else 0) ∧
    (∑' k : ℕ, if (4:ℝ)^k < w then (4:ℝ)^k else 0) ≤ (4/3:ℝ)*w := by
  classical
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt w (by norm_num : (1:ℝ) < 4)
  have hz (k : ℕ) (hk : k ∉ Finset.range N) :
      (if (4:ℝ)^k < w then (4:ℝ)^k else 0) = 0 := by
    have hNk : N ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hpow : (4:ℝ)^N ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hNk
    exact ite_eq_right (not_lt.mpr (hN.le.trans hpow))
  refine ⟨summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  exact dyadic_tail_partial_le hw N

lemma pow_eight_two_thirds (k : ℕ) :
    ((8:ℝ)^k)^(2/3:ℝ) = (4:ℝ)^k := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]
  congr 1
  have he : (8:ℝ) = (2:ℝ)^(3:ℝ) := by norm_num
  rw [he, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma dyadic_density_bound {B r : ℝ} (hB : 0 < B) (hr : 0 ≤ r)
    (h : ℕ → ℝ) (h0 : ∀ k, 0 ≤ h k)
    (hs : Summable (fun k => (4:ℝ)^k * h k))
    (hcap : ∀ k, r ≤ 2*B*(8:ℝ)^k + 2*h k) :
    r^(5/3:ℝ) ≤ (32*B)^(2/3:ℝ)*r +
      (4*(32*B)^(2/3:ℝ))*(∑' k, (4:ℝ)^k*h k) := by
  have hS : 0 ≤ ∑' k, (4:ℝ)^k*h k := tsum_nonneg (fun k => mul_nonneg (by positivity) (h0 k))
  have hfac : 0 ≤ (32*B)^(2/3:ℝ) := Real.rpow_nonneg (by positivity) _
  have hrpow : r^(5/3:ℝ) = r^(2/3:ℝ)*r := by
    by_cases hz : r = 0
    · simp [hz]
    · rw [show (5/3:ℝ) = 2/3+1 by norm_num, Real.rpow_add_one hz]
  by_cases hsmall : r ≤ 4*B
  · have hb : r^(2/3:ℝ) ≤ (32*B)^(2/3:ℝ) :=
      Real.rpow_le_rpow hr (hsmall.trans (by linarith)) (by norm_num)
    rw [hrpow]
    have ht := mul_le_mul_of_nonneg_right hb hr
    nlinarith [mul_nonneg hfac hS]
  · have hbig : 4*B < r := lt_of_not_ge hsmall
    obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near
      ((le_div_iff₀ (by positivity : (0:ℝ) < 4*B)).2 (by linarith : 1*(4*B) ≤ r))
      (by norm_num : (1:ℝ) < 8)
    have hlo : 4*B*(8:ℝ)^k ≤ r := by
      have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*B)).mp hk
      nlinarith
    have hup : r ≤ 32*B*(8:ℝ)^k := by
      have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 4*B)).mp hk'
      rw [pow_succ] at hh
      nlinarith
    have hh : r ≤ 4*h k := by have hc := hcap k; linarith
    have hpower : r^(2/3:ℝ) ≤ (32*B)^(2/3:ℝ)*(4:ℝ)^k := by
      have H := Real.rpow_le_rpow hr hup (by norm_num : (0:ℝ) ≤ 2/3)
      rwa [Real.mul_rpow (by positivity) (by positivity), pow_eight_two_thirds] at H
    have hsingle : (4:ℝ)^k*h k ≤ ∑' j, (4:ℝ)^j*h j :=
      hs.le_tsum k (fun j _ => mul_nonneg (by positivity) (h0 j))
    rw [hrpow]
    calc
      _ ≤ ((32*B)^(2/3:ℝ)*(4:ℝ)^k)*(4*h k) :=
        mul_le_mul hpower hh hr (by positivity)
      _ = (4*(32*B)^(2/3:ℝ))*((4:ℝ)^k*h k) := by ring
      _ ≤ (4*(32*B)^(2/3:ℝ))*(∑' j, (4:ℝ)^j*h j) :=
        mul_le_mul_of_nonneg_left hsingle (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hfac hr)

lemma dyadic_spectral_tail_bound {α : Type*} (w c : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hc : ∀ a, 0 ≤ c a)
    (hs : Summable (fun a => w a*c a)) :
    Summable (fun k : ℕ => (4:ℝ)^k * (∑' a, if (4:ℝ)^k < w a then c a else 0)) ∧
    (∑' k : ℕ, (4:ℝ)^k * (∑' a, if (4:ℝ)^k < w a then c a else 0)) ≤
      (4/3:ℝ)*(∑' a, w a*c a) := by
  classical
  let F (a : α) (k : ℕ) := (if (4:ℝ)^k < w a then (4:ℝ)^k else 0)*c a
  have hF0 (a : α) (k : ℕ) : 0 ≤ F a k := by
    dsimp only [F]
    apply mul_nonneg _ (hc a)
    split_ifs <;> positivity
  have hFa (a : α) : Summable (F a) :=
    (dyadic_tail_hasSum (hw a)).1.mul_right (c a)
  have hFb (a : α) : (∑' k, F a k) ≤ (4/3:ℝ)*(w a*c a) := by
    rw [show (∑' k, F a k) = (∑' k, if (4:ℝ)^k < w a then (4:ℝ)^k else 0)*c a from
      tsum_mul_right]
    have H := mul_le_mul_of_nonneg_right (dyadic_tail_hasSum (hw a)).2 (hc a)
    simpa only [mul_assoc] using H
  have houter : Summable (fun a => ∑' k, F a k) :=
    Summable.of_nonneg_of_le (fun a => tsum_nonneg (hF0 a)) hFb (hs.mul_left (4/3:ℝ))
  have hprod : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg (fun z => hF0 z.1 z.2)).2 ⟨hFa,houter⟩
  have heq (k : ℕ) : (∑' a, F a k) =
      (4:ℝ)^k*(∑' a, if (4:ℝ)^k < w a then c a else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro a
    dsimp only [F]
    split_ifs <;> simp only [zero_mul, mul_zero]
  refine ⟨?_, ?_⟩
  · simpa only [Prod.swap_prod_mk, Function.uncurry_apply_pair, heq] using hprod.prod_symm.prod
  · simp_rw [← heq]
    rw [hprod.tsum_comm]
    have H := houter.tsum_le_tsum hFb (hs.mul_left (4/3:ℝ))
    simpa only [tsum_mul_left] using H

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Weighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma FermionicCoefficients.weighted_eq {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    (w : α → ℝ) (i j : Fin n) :
    (∑' b, w (b i) * ‖f b‖^2) = ∑' b, w (b j) * ‖f b‖^2 := by
  classical
  let p := Equiv.swap i j
  have he := (coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => w (b i) * ‖f b‖^2)
  change (∑' b, w ((b ∘ p) i) * ‖f (b ∘ p)‖^2) = _ at he
  simp only [Function.comp_apply, p, Equiv.swap_apply_left, hf.norm_permute] at he
  exact he.symm

lemma FermionicCoefficients.weighted_summable {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hs : Summable (fun b => (∑ j, w (b j)) * ‖f b‖^2)) (i : Fin n) :
    Summable (fun b => w (b i) * ‖f b‖^2) := by
  apply Summable.of_nonneg_of_le (fun b => mul_nonneg (hw _) (sq_nonneg _)) _ hs
  intro b
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hw (b j)) (Finset.mem_univ i)) (sq_nonneg _)

lemma FermionicCoefficients.weighted_sum {n : ℕ} {α : Type*}
    {f : (Fin n → α) → ℂ} (hf : FermionicCoefficients f)
    {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hs : Summable (fun b => (∑ j, w (b j)) * ‖f b‖^2)) (i : Fin n) :
    (n : ℝ) * (∑' b, w (b i) * ‖f b‖^2) =
      ∑' b, (∑ j, w (b j)) * ‖f b‖^2 := by
  simp_rw [Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun j _ => weighted_summable hw hs j)]
  simp_rw [hf.weighted_eq w _ i]
  simp

end Coulomb
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma nonneg_integrable_series {A ι : Type*} [MeasurableSpace A] [Countable ι]
    {μ : Measure A} (F : ι → A → ℝ) (hF0 : ∀ i x, 0 ≤ F i x)
    (hFi : ∀ i, Integrable (F i) μ) (hs : Summable (fun i => ∫ x, F i x ∂μ)) :
    (∀ᵐ x ∂μ, Summable (fun i => F i x)) ∧
    Integrable (fun x => ∑' i, F i x) μ ∧
    (∫ x, ∑' i, F i x ∂μ) = ∑' i, ∫ x, F i x ∂μ := by
  have hm (i : ι) : AEMeasurable (fun x => ENNReal.ofReal (F i x)) μ :=
    (hFi i).1.aemeasurable.ennreal_ofReal
  have he (i : ι) : eLpNorm (F i) 1 μ = ENNReal.ofReal (∫ x, F i x ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [Real.enorm_of_nonneg (hF0 i _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hFi i) (ae_of_all μ (hF0 i))).symm
  have hfin : (∑' i, eLpNorm (F i) 1 μ) ≠ ∞ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (hF0 i)) hs]
    exact ENNReal.ofReal_ne_top
  have has : ∀ᵐ x ∂μ, Summable (fun i => F i x) := by
    have H := summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun i => (hFi i).1) hfin
    simpa only [Real.norm_of_nonneg (hF0 _ _)] using H
  have hsum : (∫⁻ x, ∑' i, ENNReal.ofReal (F i x) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hm]
    convert hfin using 2
    all_goals try with_reducible_and_instances rfl
    funext i
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [Real.enorm_of_nonneg (hF0 _ _)]
  have ht := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hsum
  have hti : Integrable (fun x => ∑' i, F i x) μ := by
    apply ht.congr
    filter_upwards [has] with x hx
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hF0 i x) hx,
      ENNReal.toReal_ofReal (tsum_nonneg (fun i => hF0 i x))]
  refine ⟨has, hti, ?_⟩
  exact (integral_tsum_of_summable_integral_norm hFi
    (by simpa only [Real.norm_of_nonneg (hF0 _ _)] using hs)).symm

lemma firstParticleDensity_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    Integrable (firstParticleDensity (μ := μ) f) μ :=
  (firstFiber_memLp hf).norm.integrable_sq.integral_prod_right.const_mul _

lemma highParticleDensity_integrable {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) (s : Finset ι) :
    Integrable (highParticleDensity (μ := μ) v s f) μ :=
  (highProjection_memLp v hv s (firstFiber_memLp hf)).norm.integrable_sq.integral_prod_right.const_mul _

lemma highParticleDensity_integral {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : Finset ι) :
    (∫ x, highParticleDensity (μ := μ) v s f x ∂μ) =
      ((n+1:ℕ):ℝ)*(∑' b, if b 0 ∈ s then 0 else ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  simp only [highParticleDensity]
  rw [integral_const_mul, ← integral_prod_symm _
    (highProjection_memLp v hv s (firstFiber_memLp hf)).norm.integrable_sq,
      highProjection_norm_spectrum v hv ho hc hf s]

lemma high_density_spectral_series {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (ha : ProductAntisymmetric (μ := μ) f)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : ℕ → Finset ι) (w : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hcut : ∀ k a, a ∉ s k → (4:ℝ)^k < w a)
    (hs : Summable (fun b : Fin (n+1) → ι => (∑ j, w (b j))*
      ‖scalarCoefficient (μ := μ) f v b‖^2)) :
    Summable (fun k : ℕ => (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ∧
    (∑' k : ℕ, (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ≤
      (4/3:ℝ)*(∑' b : Fin (n+1) → ι, (∑ j, w (b j))*
        ‖scalarCoefficient (μ := μ) f v b‖^2) := by
  classical
  let c := scalarCoefficient (μ := μ) f v
  have hc2 : Summable (fun b => ‖c b‖^2) := scalarCoefficient_summable f hf v hv ho
  have hsingle := FermionicCoefficients.weighted_summable hw hs (0 : Fin (n+1))
  have H := dyadic_spectral_tail_bound (fun b : Fin (n+1) → ι => w (b 0))
    (fun b => ‖c b‖^2) (fun b => hw (b 0)) (fun b => sq_nonneg _) hsingle
  have hsum (k : ℕ) : Summable (fun b : Fin (n+1) → ι =>
      if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) :=
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> simp) hc2
  have hcomp (k : ℕ) : (∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ) ≤
      ((n+1:ℕ):ℝ)*(∑' b : Fin (n+1) → ι, if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
    rw [highParticleDensity_integral hf v hv ho hc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Summable.tsum_le_tsum _ _ (hsum k)
    · intro b
      by_cases hb : b 0 ∈ s k
      · simp only [hb, ite_true]; positivity
      · simp only [hb, ite_false, hcut k (b 0) hb, ite_true]
        exact le_rfl
    · change Summable (fun b => if b 0 ∈ s k then 0 else ‖c b‖^2)
      exact Summable.of_nonneg_of_le (fun b => by positivity)
        (fun b => by split_ifs <;> simp) hc2
  have hl (k : ℕ) : 0 ≤ (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun x => mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _)))
  have hb (k : ℕ) : (4:ℝ)^k * ∫ x, highParticleDensity (μ := μ) v (s k) f x ∂μ ≤
      ((n+1:ℕ):ℝ)*((4:ℝ)^k * ∑' b : Fin (n+1) → ι,
        if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
    simpa only [mul_left_comm ((4:ℝ)^k)] using mul_le_mul_of_nonneg_left (hcomp k) (by positivity : 0 ≤ (4:ℝ)^k)
  have hs' := Summable.of_nonneg_of_le hl hb (H.1.mul_left ((n+1:ℕ):ℝ))
  refine ⟨hs', ?_⟩
  calc
    _ ≤ ((n+1:ℕ):ℝ)*(∑' k : ℕ, (4:ℝ)^k * ∑' b : Fin (n+1) → ι,
        if (4:ℝ)^k < w (b 0) then ‖c b‖^2 else 0) := by
      simpa only [tsum_mul_left] using hs'.tsum_le_tsum hb (H.1.mul_left ((n+1:ℕ):ℝ))
    _ ≤ ((n+1:ℕ):ℝ)*((4/3:ℝ)*(∑' b : Fin (n+1) → ι, w (b 0)*‖c b‖^2)) :=
      mul_le_mul_of_nonneg_left H.2 (by positivity)
    _ = _ := by
      rw [mul_left_comm, (scalarCoefficient_antisymmetric ha v).weighted_sum hw hs]

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FirstParticleDensityNonneg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma firstParticleDensity_nonneg {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (f : (Fin (n+1) → A) → ℂ) (x : A) :
    0 ≤ firstParticleDensity (μ := μ) f x :=
  mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _))

lemma highParticleDensity_nonneg {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} {n : ℕ} (v : ι → A → ℂ) (s : Finset ι)
    (f : (Fin (n+1) → A) → ℂ) (x : A) :
    0 ≤ highParticleDensity (μ := μ) v s f x :=
  mul_nonneg (by positivity) (integral_nonneg (fun y => sq_nonneg _))

lemma firstParticleDensity_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) :
    (∫ x, firstParticleDensity (μ := μ) f x ∂μ) =
      ((n+1:ℕ):ℝ)*(∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) := by
  simp only [firstParticleDensity]
  rw [integral_const_mul, ← integral_prod_symm _ (firstFiber_memLp hf).norm.integrable_sq,
    ← firstUnfiber_norm_sq]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp [firstUnfiber, firstFiber, Fin.cons_self_tail])

lemma memLp_fiber_right_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => f (y,x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hf.norm.integrable_sq.prod_left_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

lemma first_density_low_high_cap {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [SecondCountableTopology (Lp ℂ 2 μ)] {n : ℕ}
    {f : (Fin (n+1) → A) → ℂ} (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (ha : ProductAntisymmetric (μ := μ) f)
    (hn : (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) ≤ 1)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (s : ℕ → Finset ι) {B : ℝ}
    (hdiag : ∀ k x, (∑ i ∈ s k, ‖v i x‖^2) ≤ B*(8:ℝ)^k) :
    ∀ᵐ x ∂μ, ∀ k, firstParticleDensity (μ := μ) f x ≤ 2*B*(8:ℝ)^k +
      2*highParticleDensity (μ := μ) v (s k) f x := by
  filter_upwards [memLp_fiber_right_ae (firstFiber_memLp hf)] with x hx k
  have hp := lowProjection_density_pauli f hf ha v hv ho (s k) x
  have hp' : ((n+1:ℕ):ℝ) * (∫ y : Fin n → A,
      ‖lowProjection (μ := μ) v (s k) (firstFiber f) (y,x)‖^2 ∂(Measure.pi fun _ => μ)) ≤
      ∑ i ∈ s k, ‖v i x‖^2 := by
    apply hp.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
      (Finset.sum_nonneg (fun i _ => sq_nonneg (‖v i x‖)))
  have hh := fiber_norm_sq_split hx (lowProjection_tail_memLp v hv (s k) (firstFiber_memLp hf) x)
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ((n+1:ℕ):ℝ))
  have hd := hdiag k x
  dsimp only [firstParticleDensity, highParticleDensity, highProjection, Pi.sub_apply]
  nlinarith only [hh', hp', hd]

lemma continuum_rumin_bound {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] [Countable ι] [SecondCountableTopology (Lp ℂ 2 μ)]
    {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) (ha : ProductAntisymmetric (μ := μ) f)
    (hn : (∫ z, ‖f z‖^2 ∂(Measure.pi fun _ => μ)) ≤ 1)
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hc : CompleteOrbitals μ v) (s : ℕ → Finset ι) (w : ι → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hcut : ∀ k a, a ∉ s k → (4:ℝ)^k < w a)
    {B : ℝ} (hB : 0 < B) (hdiag : ∀ k x, (∑ i ∈ s k, ‖v i x‖^2) ≤ B*(8:ℝ)^k)
    (hs : Summable (fun b : Fin (n+1) → ι => (∑ j, w (b j))*
      ‖scalarCoefficient (μ := μ) f v b‖^2)) :
    Integrable (fun x => (firstParticleDensity (μ := μ) f x)^(5/3:ℝ)) μ ∧
    (∫ x, (firstParticleDensity (μ := μ) f x)^(5/3:ℝ) ∂μ) ≤
      (32*B)^(2/3:ℝ)*((n+1:ℕ):ℝ) + (16/3:ℝ)*(32*B)^(2/3:ℝ) *
        (∑' b : Fin (n+1) → ι, (∑ j, w (b j))*‖scalarCoefficient (μ := μ) f v b‖^2) := by
  let r := firstParticleDensity (μ := μ) f
  let h (k : ℕ) := highParticleDensity (μ := μ) v (s k) f
  let C := (32*B)^(2/3:ℝ)
  have hC : 0 ≤ C := Real.rpow_nonneg (by positivity) _
  have hr0 (x : A) : 0 ≤ r x := firstParticleDensity_nonneg f x
  have hh0 (k : ℕ) (x : A) : 0 ≤ h k x := highParticleDensity_nonneg v (s k) f x
  have hri : Integrable r μ := firstParticleDensity_integrable hf
  have hhi (k : ℕ) : Integrable (h k) μ := highParticleDensity_integrable hf v hv (s k)
  have hspec := high_density_spectral_series hf ha v hv ho hc s w hw hcut hs
  have hser := nonneg_integrable_series (fun k x => (4:ℝ)^k*h k x)
    (fun k x => mul_nonneg (by positivity) (hh0 k x))
    (fun k => (hhi k).const_mul ((4:ℝ)^k))
    (by simpa only [integral_const_mul] using hspec.1)
  have hcap := first_density_low_high_cap hf ha hn v hv ho s hdiag
  have hbound : ∀ᵐ x ∂μ, (r x)^(5/3:ℝ) ≤ C*r x + (4*C)*(∑' k, (4:ℝ)^k*h k x) := by
    filter_upwards [hser.1, hcap] with x hx hc'
    exact dyadic_density_bound hB (hr0 x) (fun k => h k x) (fun k => hh0 k x) hx hc'
  have hright : Integrable (fun x => C*r x+(4*C)*(∑' k, (4:ℝ)^k*h k x)) μ :=
    (hri.const_mul C).add (hser.2.1.const_mul (4*C))
  have hl : Integrable (fun x => (r x)^(5/3:ℝ)) μ := by
    apply hright.mono' ((hri.1.aemeasurable.pow_const (5/3:ℝ)).aestronglyMeasurable)
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (hr0 x) _)] using hx
  refine ⟨hl, ?_⟩
  have H := integral_mono_ae hl hright hbound
  rw [integral_add (hri.const_mul C) (hser.2.1.const_mul (4*C)),
    integral_const_mul, integral_const_mul, hser.2.2] at H
  simp_rw [integral_const_mul] at H
  have hm : (∫ x, r x ∂μ) ≤ ((n+1:ℕ):ℝ) := by
    rw [firstParticleDensity_integral hf]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ ((n+1:ℕ):ℝ))
  have hm' := mul_le_mul_of_nonneg_left hm hC
  have he := mul_le_mul_of_nonneg_left hspec.2 (by positivity : 0 ≤ 4*C)
  dsimp only [C] at H he hm'
  nlinarith only [H, he, hm']

lemma neumannMode_sq_bound {b : ℝ} (hb : 0 < b) (q : ℕ) (x : ℝ) :
    ‖neumannMode b q x‖^2 ≤ 2/b := by
  have hw : 0 < cosineWeight b q := by unfold cosineWeight; split_ifs <;> positivity
  have he : ‖neumannMode b q x‖^2 =
      (Real.cos ((q : ℝ)*Real.pi*x/b))^2 / cosineWeight b q := by
    change ‖(((Real.sqrt (cosineWeight b q))⁻¹ : ℝ) : ℂ) *
      (Real.cos ((q : ℝ)*Real.pi*x/b) : ℂ)‖^2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hw.le]
    ring
  rw [he]
  calc
    _ ≤ 1 / cosineWeight b q := div_le_div_of_nonneg_right (Real.cos_sq_le_one _) hw.le
    _ ≤ 2/b := by unfold cosineWeight; split_ifs <;> field_simp <;> nlinarith

lemma cubeMode_sq_bound {b : ℝ} (hb : 0 < b) (q : Fin 3 → ℕ) (x : Fin 3 → ℝ) :
    ‖cubeMode b q x‖^2 ≤ 8/b^3 := by
  calc
    _ = ∏ i : Fin 3, ‖neumannMode b (q i) (x i)‖^2 := by
      simp only [cubeMode, norm_prod, Finset.prod_pow]
    _ ≤ ∏ i : Fin 3, (2/b) := Finset.prod_le_prod
      (fun i _ => sq_nonneg _) (fun i _ => neumannMode_sq_bound hb (q i) (x i))
    _ = _ := by simp; ring

lemma spinCubeMode_sq_bound {b : ℝ} (hb : 0 < b) (a : SpinMode)
    (x : Fin 2 × (Fin 3 → ℝ)) : ‖spinCubeMode b a x‖^2 ≤ 8/b^3 := by
  by_cases hs : x.1 = a.1
  · simpa only [spinCubeMode, spinDelta, hs, ite_true, one_mul] using cubeMode_sq_bound hb a.2 x.2
  · simp only [spinCubeMode, spinDelta, hs, ite_false, zero_mul, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

lemma coarseCubeModes_card (k : ℕ) : (coarseCubeModes k).card = 2*(2^k+1)^3 := by
  simp [coarseCubeModes, Fintype.card_piFinset]

lemma coarseCubeModes_card_le (k : ℕ) : ((coarseCubeModes k).card : ℝ) ≤ 16*(8:ℝ)^k := by
  rw [coarseCubeModes_card]
  push_cast
  have hq : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  calc
    _ ≤ 2*(2*(2:ℝ)^k)^3 := by gcongr; linarith
    _ = 16*(8:ℝ)^k := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 3, pow_mul]
      norm_num
      ring

lemma spinCubeMode_diagonal {b : ℝ} (hb : 0 < b) (k : ℕ)
    (x : Fin 2 × (Fin 3 → ℝ)) :
    (∑ a ∈ coarseCubeModes k, ‖spinCubeMode b a x‖^2) ≤ (128/b^3)*(8:ℝ)^k := by
  calc
    _ ≤ ∑ a ∈ coarseCubeModes k, (8/b^3) := Finset.sum_le_sum
      (fun a _ => spinCubeMode_sq_bound hb a x)
    _ = ((coarseCubeModes k).card : ℝ)*(8/b^3) := by simp
    _ ≤ (16*(8:ℝ)^k)*(8/b^3) := mul_le_mul_of_nonneg_right (coarseCubeModes_card_le k) (by positivity)
    _ = _ := by ring

lemma coarseCubeModes_cutoff (k : ℕ) (a : SpinMode) (ha : a ∉ coarseCubeModes k) :
    (4:ℝ)^k < (latticeRadius a.2)^2 := by
  classical
  rcases a with ⟨a,q⟩
  have hn : ¬ ∀ i, q i < 2^k+1 := by
    intro h
    exact ha (Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (h i))⟩)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hi' : (2:ℝ)^k < (q i : ℝ) := by exact_mod_cast (show 2^k < q i by omega)
  have he : ((2:ℝ)^k)^2 = (4:ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have ht : ((q i : ℝ))^2 ≤ (latticeRadius q)^2 := by
    simp only [latticeRadius, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum (f := fun j => (q j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hz : 0 ≤ (2:ℝ)^k := by positivity
  nlinarith

end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeLabelEquiv
attribute [-instance] _root_.OAI.Coulomb.spinCubeMeasure_isFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma spinCubeMode_inner {b : ℝ} (hb : 0 < b) (a c : SpinMode) :
    (∫ x, star (spinCubeMode b a x) * spinCubeMode b c x ∂(spinCubeMeasure b)) =
      if a = c then (1 : ℂ) else 0 := by
  classical
  rw [show (fun x => star (spinCubeMode b a x) * spinCubeMode b c x) =
    fun x => (star (spinDelta a.1 x.1) * spinDelta c.1 x.1) *
      (star (cubeMode b a.2 x.2) * cubeMode b c.2 x.2) by
    funext x; simp only [spinCubeMode, star_mul]; ring]
  rw [spinCubeMeasure, integral_prod_mul
    (fun q => star (spinDelta a.1 q) * spinDelta c.1 q)
    (fun x => star (cubeMode b a.2 x) * cubeMode b c.2 x), spinDelta_inner,
    show (∫ x, star (cubeMode b a.2 x) * cubeMode b c.2 x ∂(cubeMeasure b 3)) =
      if a.2 = c.2 then (1 : ℂ) else 0 from
      by
        have H := scalarTensor_orthonormal (μ := volume.restrict (Ioc 0 b))
          (neumannMode b) (fun i j => by
            by_cases hij : i = j
            · simpa only [ite_eq_left hij] using neumannMode_orthonormal hb i j
            · simpa only [ite_eq_right hij] using neumannMode_orthonormal hb i j) a.2 c.2
        by_cases h : a.2 = c.2
        · simpa only [cubeMode, cubeMeasure, ite_eq_left h] using H
        · simpa only [cubeMode, cubeMeasure, ite_eq_right h] using H]
  by_cases h1 : a.1 = c.1 <;> by_cases h2 : a.2 = c.2 <;>
    simp [h1, h2, Prod.ext_iff]

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

lemma spinCubeEquiv_measurePreserving (n : ℕ) (b : ℝ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinCubeMeasure b)
      (Measure.count.prod (finiteCubeMeasure b (Fin n × Fin 3))) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => cubeMeasure b 3)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume.restrict (Ioc 0 b)))
  exact h2.comp h1

lemma H1Vector.spinCube_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.value sx.1 (WithLp.toLp 2 sx.2)) 2
      (Measure.count.prod (finiteCubeMeasure b (Fin n × Fin 3))) := by
  classical
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ =>
    tensorPair_memLp (hi s) (ψ.cube_memLp b s))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma H1Vector.cubeState_memLp {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinCubeMeasure b) :=
  (ψ.spinCube_memLp b).comp_measurePreserving (spinCubeEquiv_measurePreserving n b)

lemma cubeState_mass {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinCubeMeasure b)) = cubeMass ψ b := by
  have H := (spinCubeEquiv_measurePreserving n b).integral_comp'
    (fun sx => ‖ψ.value sx.1 (WithLp.toLp 2 sx.2)‖^2)
  change (∫ z, ‖cubeState ψ z‖^2 ∂(Measure.pi fun _ : Fin n => spinCubeMeasure b)) = _ at H
  rw [H, integral_prod _ ((ψ.spinCube_memLp b).norm.integrable_sq), integral_count]
  rfl

lemma cubeState_antisymmetric {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ) (b : ℝ) :
    ProductAntisymmetric (μ := spinCubeMeasure b) (cubeState ψ) := by
  intro p
  have hs (s : Spins n) : ∀ᵐ x ∂(finiteCubeMeasure b (Fin n × Fin 3)),
      ψ.value (s ∘ p) (permute p (WithLp.toLp 2 x)) =
        ((p.sign : ℤ) : ℂ) * ψ.value s (WithLp.toLp 2 x) :=
    ((PiLp.volume_preserving_toLp (Fin n × Fin 3)).quasiMeasurePreserving.ae (hψ p s)).filter_mono
      (ae_mono (finiteCubeMeasure_le_volume b))
  have hall := (ae_all_iff.mpr hs)
  have hp := (Measure.quasiMeasurePreserving_snd (μ := (Measure.count : Measure (Spins n)))).ae hall
  have ht := (spinCubeEquiv_measurePreserving n b).quasiMeasurePreserving.ae hp
  filter_upwards [ht] with z hz
  exact hz (fun i => (z i).1)

lemma spinCube_tensor_delta {n : ℕ} (b : ℝ) (a : Fin n → SpinMode)
    (sx : Spins n × ((Fin n × Fin 3) → ℝ)) :
    (∏ i, spinCubeMode b (a i) ((spinCubeEquiv n).symm sx i)) =
      (if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        finiteCubeMode b (cubeLabelEquiv n a).2 sx.2 := by
  classical
  change (∏ i, (if sx.1 i = (a i).1 then (1:ℂ) else 0) *
    ∏ j, neumannMode b ((a i).2 j) (sx.2 (i,j))) = _
  rw [Finset.prod_mul_distrib]
  have he : (∏ i, if sx.1 i = (a i).1 then (1:ℂ) else 0) =
      if sx.1 = (cubeLabelEquiv n a).1 then 1 else 0 := by
    by_cases h : sx.1 = (cubeLabelEquiv n a).1
    · simp only [h, cubeLabelEquiv, Equiv.coe_fn_mk, ite_true, Finset.prod_const_one]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  rw [he]
  congr 1
  simp only [finiteCubeMode, Fintype.prod_prod_type, cubeLabelEquiv, Equiv.coe_fn_mk]

lemma cubeState_coefficient {n : ℕ} (ψ : H1Vector n) (b : ℝ) (a : Fin n → SpinMode) :
    scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a =
      cubeFermionCoefficient ψ b a := by
  classical
  unfold scalarCoefficient
  rw [← (spinCubeEquiv_measurePreserving n b).symm.integral_comp']
  simp only [spinCube_tensor_delta]
  have he (sx : Spins n × ((Fin n × Fin 3) → ℝ)) :
      star ((if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        finiteCubeMode b (cubeLabelEquiv n a).2 sx.2) * cubeState ψ ((spinCubeEquiv n).symm sx) =
      (if sx.1 = (cubeLabelEquiv n a).1 then (1:ℂ) else 0) *
        (star (finiteCubeMode b (cubeLabelEquiv n a).2 sx.2) *
          ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 sx.2)) := by
    by_cases h : sx.1 = (cubeLabelEquiv n a).1
    · simp only [ite_eq_left h, one_mul]
      change star _ * ψ.value sx.1 (WithLp.toLp 2 sx.2) = _
      rw [h]
    · simp only [ite_eq_right h, zero_mul, star_zero]
  simp_rw [he]
  rw [integral_prod_mul (fun s : Spins n => if s = (cubeLabelEquiv n a).1 then (1:ℂ) else 0)
    (fun x => star (finiteCubeMode b (cubeLabelEquiv n a).2 x) *
      ψ.value (cubeLabelEquiv n a).1 (WithLp.toLp 2 x)), integral_count]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_mul]
  rfl

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CubeMassMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma cubeMass_le_mass {n : ℕ} (ψ : H1Vector n) (b : ℝ) : cubeMass ψ b ≤ mass ψ := by
  apply Finset.sum_le_sum
  intro s _
  calc
    _ ≤ ∫ x : (Fin n × Fin 3) → ℝ, ‖ψ.value s (WithLp.toLp 2 x)‖^2 :=
      integral_mono_measure (finiteCubeMeasure_le_volume b) (ae_of_all _ (fun x => sq_nonneg _))
        ((ψ.value_L2 s).comp_measurePreserving (PiLp.volume_preserving_toLp _)).norm.integrable_sq
    _ = _ := (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
      PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma cubeKinetic_le_kinetic {n : ℕ} (ψ : H1Vector n) (b : ℝ) :
    cubeKinetic ψ b ≤ kinetic ψ := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ∫ x : (Fin n × Fin 3) → ℝ, ‖ψ.gradient s i (WithLp.toLp 2 x)‖^2 :=
      integral_mono_measure (finiteCubeMeasure_le_volume b) (ae_of_all _ (fun x => sq_nonneg _))
        ((ψ.partial_L2 s i).comp_measurePreserving (PiLp.volume_preserving_toLp _)).norm.integrable_sq
    _ = _ := (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
      PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.gradient s i x‖^2)

lemma cubeState_weighted {n : ℕ} (ψ : H1Vector n) {b : ℝ} (hb : 0 < b)
    (a : Fin n → SpinMode) :
    (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2 =
      (2*b^2/Real.pi^2)*(cubeSpectralWeight b a*‖cubeFermionCoefficient ψ b a‖^2) := by
  rw [cubeState_coefficient, cubeSpectralWeight_eq_neumann, ← Finset.mul_sum]
  field_simp

lemma cubeState_weighted_summable {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    Summable (fun a : Fin n → SpinMode => (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2) := by
  simp_rw [cubeState_weighted ψ hb]
  exact (cubeFermionCoefficient_energy_summable hn ψ hb).mul_left _

lemma cubeState_weighted_le {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    {b : ℝ} (hb : 0 < b) :
    (∑' a : Fin n → SpinMode, (∑ j, (latticeRadius (a j).2)^2) *
      ‖scalarCoefficient (μ := spinCubeMeasure b) (cubeState ψ) (spinCubeMode b) a‖^2) ≤
      (2*b^2/Real.pi^2)*kinetic ψ := by
  simp_rw [cubeState_weighted ψ hb, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left ((cubeFermionCoefficient_energy_le hn ψ hb).trans
    (cubeKinetic_le_kinetic ψ b)) (by positivity)

lemma cubeRumin_constant {b : ℝ} (hb : 0 < b) :
    (32*(128/b^3))^(2/3:ℝ) = 256/b^2 := by
  rw [show 32*(128/b^3)=(16/b)^3 by ring, ← Real.rpow_natCast_mul (by positivity : 0 ≤ 16/b)]
  norm_num
  ring

theorem cube_density_power_bound {n : ℕ} (ψ : H1Vector (n+1)) (hψ : Antisymmetric ψ)
    (hm : mass ψ ≤ 1) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => (firstParticleDensity (μ := spinCubeMeasure b) (cubeState ψ) x)^(5/3:ℝ))
      (spinCubeMeasure b) ∧
    (∫ x, (firstParticleDensity (μ := spinCubeMeasure b) (cubeState ψ) x)^(5/3:ℝ)
      ∂(spinCubeMeasure b)) ≤ (256/b^2)*((n+1:ℕ):ℝ) + (8192/(3*Real.pi^2))*kinetic ψ := by
  let : Fact ((2:ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (spinCubeMeasure b) := isSeparable_of_sigmaFinite _
  have H := continuum_rumin_bound (ψ.cubeState_memLp b) (cubeState_antisymmetric hψ b)
    (by rw [cubeState_mass]; exact (cubeMass_le_mass ψ b).trans hm)
    (spinCubeMode b) (spinCubeMode_memLp b) (fun i j => by by_cases h : i = j <;> simpa [h] using spinCubeMode_inner hb i j) (spinCubeMode_complete hb)
    coarseCubeModes (fun a : SpinMode => (latticeRadius a.2)^2) (fun a => sq_nonneg _)
    coarseCubeModes_cutoff (by positivity : 0 < 128/b^3) (spinCubeMode_diagonal hb)
    (cubeState_weighted_summable (by omega) ψ hb)
  refine ⟨H.1, ?_⟩
  rw [cubeRumin_constant hb] at H
  have ht := cubeState_weighted_le (by omega) ψ hb
  calc
    _ ≤ _ := H.2
    _ ≤ (256/b^2)*((n+1:ℕ):ℝ)+(16/3:ℝ)*(256/b^2)*((2*b^2/Real.pi^2)*kinetic ψ) := by
      gcongr
    _ = _ := by field_simp; ring

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Translate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
lemma centeredSpinCube_measurable (R : ℝ) : MeasurableSet (centeredSpinCube R) :=
  MeasurableSet.univ.prod (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))

lemma spinShift_measurePreserving (t : Fin 3 → ℝ) :
    MeasurePreserving (spinShift t) spinSpaceMeasure spinSpaceMeasure :=
  (MeasurePreserving.id Measure.count).prod (measurePreserving_add_right volume t)

lemma spinCubeMeasure_eq_restrict (b : ℝ) : spinCubeMeasure b =
    spinSpaceMeasure.restrict (univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc 0 b)) := by
  unfold spinCubeMeasure spinSpaceMeasure cubeMeasure
  rw [← Measure.restrict_pi_pi]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rfl

lemma shift_centeredCube_measurePreserving (R : ℝ) :
    MeasurePreserving (spinShift (fun _ => -R)) (spinCubeMeasure (2*R)) (centeredSpinMeasure R) := by
  have he : (spinShift (fun _ => -R)) ⁻¹' centeredSpinCube R =
      univ ×ˢ (univ.pi fun _ : Fin 3 => Ioc 0 (2*R)) := by
    ext x
    simp only [centeredSpinCube, mem_preimage, mem_prod, mem_univ, true_and, mem_univ_pi,
      mem_Ioc]
    change (∀ i, -R < x.2 i + -R ∧ x.2 i + -R ≤ R) ↔
      (∀ i, 0 < x.2 i ∧ x.2 i ≤ 2*R)
    constructor <;> intro h i <;> obtain ⟨h1,h2⟩ := h i <;> constructor <;> linarith
  refine ⟨(spinShift _).measurable, ?_⟩
  rw [spinCubeMeasure_eq_restrict, ← he, ← MeasurableEquiv.restrict_map,
    (spinShift_measurePreserving _).map_eq]
  rfl

lemma firstParticleDensity_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite ν] (e : A ≃ᵐ B)
    (he : MeasurePreserving e μ ν) {n : ℕ} (f : (Fin (n+1) → B) → ℂ) (x : A) :
    firstParticleDensity (μ := μ) (fun z => f (e ∘ z)) x =
      firstParticleDensity (μ := ν) f (e x) := by
  let E : (Fin n → A) ≃ᵐ (Fin n → B) := MeasurableEquiv.piCongrRight (fun _ => e)
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν) :=
    measurePreserving_pi _ _ (fun _ => he)
  unfold firstParticleDensity
  congr 1
  rw [← hE.integral_comp' (fun y => ‖firstFiber f (y,e x)‖^2)]
  congr 1
  funext y
  have harg : e ∘ Fin.cons x y = Fin.cons (e x) (E y) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simp only [firstFiber, harg]

lemma cubeState_translate {n : ℕ} (ψ : H1Vector n) (t : Fin 3 → ℝ)
    (z : Fin n → (Fin 2 × (Fin 3 → ℝ))) :
    cubeState (ψ.translate (commonShift t)) z = cubeState ψ ((spinShift t) ∘ z) := rfl

theorem centered_density_power_bound {n : ℕ} (ψ : H1Vector (n+1)) (hψ : Antisymmetric ψ)
    (hm : mass ψ ≤ 1) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ))
      (centeredSpinMeasure R) ∧
    (∫ x, (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ)
      ∂(centeredSpinMeasure R)) ≤ (64/R^2)*((n+1:ℕ):ℝ) + (8192/(3*Real.pi^2))*kinetic ψ := by
  have H := cube_density_power_bound (ψ.translate (commonShift (fun _ => -R)))
    (hψ.translate_common _) (by rwa [mass_translate]) (show 0 < 2*R by positivity)
  have hd (x) : firstParticleDensity (μ := spinCubeMeasure (2*R))
      (cubeState (ψ.translate (commonShift (fun _ => -R)))) x =
      firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) (spinShift (fun _ => -R) x) := by
    rw [show cubeState (ψ.translate (commonShift (fun _ => -R))) =
      (fun z => cubeState ψ ((spinShift (fun _ => -R)) ∘ z)) from
      funext (cubeState_translate ψ (fun _ => -R))]
    exact firstParticleDensity_equiv (spinShift (fun _ => -R))
      (shift_centeredCube_measurePreserving R) (cubeState ψ) x
  simp_rw [hd] at H
  refine ⟨?_, ?_⟩
  · exact ((shift_centeredCube_measurePreserving R).integrable_comp_emb
      (spinShift _).measurableEmbedding).mp H.1
  · have H2 := H.2
    rw [(shift_centeredCube_measurePreserving R).integral_comp'
      (fun x => (firstParticleDensity (μ := centeredSpinMeasure R) (cubeState ψ) x)^(5/3:ℝ)),
      kinetic_translate] at H2
    convert H2 using 1
    all_goals try with_reducible_and_instances rfl
    ring

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma integrable_and_integral_le_of_ae_tendsto {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {F : ℕ → A → ℝ} {f : A → ℝ} {u : ℕ → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hFn : ∀ n x, 0 ≤ F n x)
    (hfn : ∀ x, 0 ≤ f x)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫ x, F n x ∂μ) ≤ u n) (hu : Tendsto u atTop (𝓝 C)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hmeas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ (fun n => (hF n).1) ht
  have hfat : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hF n).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (u n)) atTop := by
        apply liminf_le_liminf (hu := isBoundedUnder_of ⟨0, fun _ => bot_le⟩)
          (hv := (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩).isCoboundedUnder_ge)
        exact Eventually.of_forall fun n => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (Eventually.of_forall (hFn n))]
          exact ENNReal.ofReal_le_ofReal (hb n)
      _ = ENNReal.ofReal C := ((ENNReal.continuous_ofReal.tendsto _).comp hu).liminf_eq
  have hf : Integrable f μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hfn _)]
    exact hfat.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hf, ?_⟩
  have hC : 0 ≤ C := ge_of_tendsto' hu fun n => (integral_nonneg (hFn n)).trans (hb n)
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hfn)]

lemma pi_exhaustion {A : Type*} {s : ℕ → Set A} (hs : Monotone s)
    (hU : (⋃ k, s k) = univ) (n : ℕ) :
    (⋃ k, (univ.pi fun _ : Fin n => s k)) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ_pi, mem_univ, iff_true]
  have hx (i : Fin n) : ∃ k, z i ∈ s k := by
    have hi : z i ∈ ⋃ k, s k := by rw [hU]; trivial
    simpa only [mem_iUnion] using hi
  choose k hk using hx
  refine ⟨Finset.univ.sup k, fun i => hs (Finset.le_sup (f := k) (Finset.mem_univ i)) (hk i)⟩

lemma density_power_exhaustion {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} {f : (Fin (n+1) → A) → ℂ}
    (hf : MemLp f 2 (Measure.pi fun _ => μ)) {s : ℕ → Set A}
    (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s) (hU : (⋃ k, s k) = univ)
    {p : ℝ} (hp : 0 < p) {u : ℕ → ℝ} {C : ℝ}
    (hi : ∀ k, Integrable (fun x => (firstParticleDensity (μ := μ.restrict (s k)) f x)^p)
      (μ.restrict (s k)))
    (hb : ∀ k, (∫ x, (firstParticleDensity (μ := μ.restrict (s k)) f x)^p ∂(μ.restrict (s k))) ≤ u k)
    (hu : Tendsto u atTop (𝓝 C)) :
    Integrable (fun x => (firstParticleDensity (μ := μ) f x)^p) μ ∧
    (∫ x, (firstParticleDensity (μ := μ) f x)^p ∂μ) ≤ C := by
  let F (k : ℕ) : A → ℝ := (s k).indicator
    (fun x => (firstParticleDensity (μ := μ.restrict (s k)) f x)^p)
  have hdn {ν : Measure A} (x : A) : 0 ≤ firstParticleDensity (μ := ν) f x :=
    mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  have hn (k) (x) : 0 ≤ F k x :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg (hdn _) p) x
  apply integrable_and_integral_le_of_ae_tendsto
    (F := F) (u := u) (fun k => (integrable_indicator_iff (hs k)).mpr (hi k)) hn
    (fun x => Real.rpow_nonneg (hdn x) p)
    ?_ (fun k => by simpa only [F, integral_indicator (hs k)] using hb k) hu
  have hslice := (firstFiber_memLp hf).norm.integrable_sq.prod_left_ae
  filter_upwards [hslice] with x hx
  have hset : (⋃ k, (univ.pi fun _ : Fin n => s k)) = univ := pi_exhaustion hmono hU n
  have hlim := tendsto_setIntegral_of_monotone
    (fun k => MeasurableSet.univ_pi (fun _ : Fin n => hs k))
    (fun k l hkl z hz i _ => hmono hkl (hz i (mem_univ i)))
    (f := fun y => ‖firstFiber f (y,x)‖^2) (μ := Measure.pi fun _ : Fin n => μ)
    (by simpa only [hset, integrableOn_univ] using hx)
  simp only [hset, Measure.restrict_univ, Measure.restrict_pi_pi] at hlim
  have hd : Tendsto (fun k => firstParticleDensity (μ := μ.restrict (s k)) f x) atTop
      (𝓝 (firstParticleDensity (μ := μ) f x)) := hlim.const_mul _
  have hpw := hd.rpow_const (Or.inr hp.le)
  have hex : ∃ k, x ∈ s k := by
    have hi : x ∈ ⋃ k, s k := by rw [hU]; trivial
    simpa only [mem_iUnion] using hi
  obtain ⟨k,hk⟩ := hex
  apply hpw.congr'
  filter_upwards [eventually_ge_atTop k] with l hl
  simp only [F, indicator_of_mem (hmono hl hk)]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma H1Vector.cubeState_full_memLp {n : ℕ} (ψ : H1Vector n) :
    MemLp (cubeState ψ) 2 (Measure.pi fun _ : Fin n => spinSpaceMeasure) :=
  ψ.spinSpace_memLp.comp_measurePreserving (spinCubeEquiv_full_measurePreserving n)

lemma centeredSpinCube_monotone : Monotone centeredSpinCube := by
  intro R S hRS x hx
  simp only [centeredSpinCube, mem_prod, mem_univ, true_and, mem_univ_pi, mem_Ioc] at *
  intro i
  obtain ⟨h1,h2⟩ := hx i
  constructor <;> linarith

lemma centeredSpinCube_exhaustion : (⋃ k : ℕ, centeredSpinCube (k+1)) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨k,hk⟩ := exists_nat_gt (‖x.2‖ : ℝ)
  refine ⟨k, ?_⟩
  simp only [centeredSpinCube, mem_prod, mem_univ, true_and, mem_univ_pi, mem_Ioc]
  intro i
  have hi : |x.2 i| ≤ ‖x.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x.2 i
  have h := abs_le.mp hi
  constructor <;> linarith

theorem global_spin_density_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) x)^(5/3:ℝ))
      spinSpaceMeasure ∧
    (∫ x, (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) x)^(5/3:ℝ)
      ∂spinSpaceMeasure) ≤ (8192/(3*Real.pi^2))*kinetic ψ := by
  apply density_power_exhaustion ψ.cubeState_full_memLp
    (s := fun k : ℕ => centeredSpinCube (k+1)) (fun k => centeredSpinCube_measurable _)
    (fun k l h => centeredSpinCube_monotone (by exact_mod_cast Nat.add_le_add_right h 1))
    centeredSpinCube_exhaustion (by norm_num : (0:ℝ) < 5/3)
    (u := fun k : ℕ => (64/(k+1:ℝ)^2)*((n+1:ℕ):ℝ)+(8192/(3*Real.pi^2))*kinetic ψ)
    (fun k => (centered_density_power_bound ψ hψ hm (by positivity : (0:ℝ)<k+1)).1)
    (fun k => (centered_density_power_bound ψ hψ hm (by positivity : (0:ℝ)<k+1)).2)
  have ht : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ((tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).comp ht)).const_mul 64
  convert (hi.mul_const ((n+1:ℕ):ℝ)).add_const ((8192/(3*Real.pi^2))*kinetic ψ) using 1 <;>
    simp [Function.comp_apply, div_eq_mul_inv]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Add
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma kinetic_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ kinetic ψ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicGapScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma mul_rpow_monomials {a : ℝ} (ha : 0<a) (c d x y : ℝ) :
    (c*a^x)*(d*a^y)=(c*d)*a^(x+y) := by rw [Real.rpow_add ha]; ring

lemma sqrt_rpow_monomial {a : ℝ} (ha : 0<a) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Real.sqrt (c*a^x)=Real.sqrt c*a^(x/2) := by
  rw [Real.sqrt_mul hc]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul ha.le]
  congr 2
  ring

lemma div_rpow_monomial {a : ℝ} (ha : 0<a) (c x y : ℝ) :
    (c*a^x)/a^y=c*a^(x-y) := by rw [Real.rpow_sub ha]; ring

lemma atomicRefinedFormula_power_expansion {a P : ℝ} (ha : 0<a) (hP : 0 ≤ P) :
    atomicRefinedFormula (a^(-349/50:ℝ)) P (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) =
      a^(-349/50:ℝ)+
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ)+
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ)+
      Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/10:ℝ)+
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ)+
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
  have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast ha.le]
    norm_num
  have hb2 : (a^(6/5:ℝ))^2=a^(12/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le]
    norm_num
  have hq : atomicPhysicalCapConstant*P*(2*a^(-3:ℝ))^2/a^2=
      (4*atomicPhysicalCapConstant*P)*a^(-8:ℝ) := by
    rw [hm2]
    calc
      _ = ((4*atomicPhysicalCapConstant*P)*a^(-6:ℝ))/a^2 := by ring
      _ = _ := by rw [←Real.rpow_natCast a 2,div_rpow_monomial ha]; norm_num
  have hn : atomicPatchCountFactor*P*(2*a^(-3:ℝ))^2=
      (4*atomicPatchCountFactor*P)*a^(-6:ℝ) := by rw [hm2]; ring
  have hd : 18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*P*(2*a^(-3:ℝ))^2=
      (72*atomicPatchCountFactor*P)*a^(-29/5:ℝ) := by
    rw [hm2]
    calc
      _ = ((72*atomicPatchCountFactor*P)*(a^(6/5:ℝ)*a^(-6:ℝ)))/a^1 := by ring
      _ = _ := by rw [←Real.rpow_add ha,←Real.rpow_natCast a 1,div_rpow_monomial ha]; norm_num
  have hqd : ((4*atomicPhysicalCapConstant*P)*a^(-8:ℝ))*
      ((72*atomicPatchCountFactor*P)*a^(-29/5:ℝ))=
      (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/5:ℝ) := by
    rw [mul_rpow_monomials ha]
    congr 1 <;> ring_nf
  have hN0 : 0 ≤ 4*atomicPatchCountFactor*P := by positivity [atomicPatchCountFactor_nonneg]
  have hQ0 : 0 ≤ 4*atomicPhysicalCapConstant*P := by positivity [atomicPhysicalCapConstant_nonneg]
  have hQD0 : 0 ≤ 288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2 := by
    positivity [atomicPhysicalCapConstant_nonneg,atomicPatchCountFactor_nonneg]
  have hn23 : ((4*atomicPatchCountFactor*P)*a^(-6:ℝ))^(2/3:ℝ)=
      (4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ) := by
    rw [Real.mul_rpow hN0 (Real.rpow_nonneg ha.le _),←Real.rpow_mul ha.le]
    norm_num
  have hsi : ((a^(6/5:ℝ))⁻¹)^2=a^(-12/5:ℝ) := by
    rw [←Real.rpow_neg ha.le,←Real.rpow_mul_natCast ha.le]
    norm_num
  unfold atomicRefinedFormula
  rw [hq,hn,hd,hqd,hb2,hsi,hn23,sqrt_rpow_monomial ha hQ0,
    sqrt_rpow_monomial ha hN0,sqrt_rpow_monomial ha hQD0]
  norm_num only
  have h1 : thinReserveFactor*(Real.sqrt P*(2*a^(-3:ℝ))/a^(12/5:ℝ))=
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ) := by
    calc
      _ = (2*thinReserveFactor*Real.sqrt P)*a^(-3:ℝ)/a^(12/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  have h2 : 12*a*unitWindowKinetic/a^(12/5:ℝ)*
      (Real.sqrt (4*atomicPhysicalCapConstant*P)*a^(-4:ℝ))=
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ) := by
    calc
      _ = (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*(a^1*a^(-4:ℝ))/a^(12/5:ℝ) := by ring
      _ = _ := by rw [←Real.rpow_natCast a 1,←Real.rpow_add ha,div_rpow_monomial ha]; norm_num
  have h4 : a^(-12/5:ℝ)*((Real.pi^2/2)*neumannBoundary)*
      ((4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ))=
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ) := by
    calc
      _ = (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*(a^(-12/5:ℝ)*a^(-4:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add ha]; norm_num
  have h5 : ((2*Real.pi+1)/(2*a^(6/5:ℝ)))*(Real.sqrt (4*atomicPatchCountFactor*P)*a^(-3:ℝ))=
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
    calc
      _ = ((((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-3:ℝ))/a^(6/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  norm_num at h1 h2 h4 h5 ⊢
  rw [h1,h2,h4,h5]

lemma atomicRefinedFormula_scaled_tendsto {P : ℝ} (hP : 0 ≤ P) :
    Tendsto (fun a : ℝ => atomicRefinedFormula (a^(-349/50:ℝ)) P
      (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)) (𝓝[>] 0) (𝓝 1) := by
  have ht := (((((tendsto_const_nhds (x := (1:ℝ))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (2*thinReserveFactor*Real.sqrt P))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<2/25)).const_mul
      (Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<29/50)).const_mul
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<139/50)).const_mul
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P)))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha : 0<a := ha
  rw [atomicRefinedFormula_power_expansion ha hP]
  simp only [add_mul,mul_assoc,←Real.rpow_add ha]
  norm_num

lemma exists_atomic_refined_small_scale : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ a : ℝ, 0<a → a < s →
      18*a^(6/5:ℝ)≤a ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) ≤ 2*a^(-349/50:ℝ) := by
  have hP : 0 ≤ atomicCountConstant := le_trans (by norm_num) atomicCountConstant_ge_two
  have he := (atomicRefinedFormula_scaled_tendsto hP).eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  have hs := ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/5)).const_mul 18).eventually
    (gt_mem_nhds (by norm_num : (18:ℝ)*0<1))
  have hh : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)<2 ∧ 18*a^(1/5:ℝ)<1 := by
    filter_upwards [he,hs, (show ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 from
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)] with a ha hb hc
    exact ⟨hc,ha,hb⟩
  obtain ⟨s,hs0,hprop⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hh
  refine ⟨min s 1, lt_min hs0 (by norm_num), min_le_right _ _, ?_⟩
  intro a ha has
  have hp := hprop ⟨ha, has.trans_le (min_le_left s 1)⟩
  constructor
  · have hx : a^(6/5:ℝ)=a^(1/5:ℝ)*a := by
      rw [show (6/5:ℝ)=1/5+1 by norm_num,Real.rpow_add ha,Real.rpow_one]
    rw [hx]
    nlinarith [mul_lt_mul_of_pos_right hp.2.2 ha]
  · have hx : a^(-349/50:ℝ)*a^(349/50:ℝ)=1 := by rw [←Real.rpow_add ha]; norm_num
    apply le_of_mul_le_mul_right (a := a^(349/50:ℝ)) _ (Real.rpow_pos_of_pos ha (349/50:ℝ))
    rw [mul_assoc,hx,mul_one]
    exact hp.2.1.le

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FreshPotentialTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma potentialForm_min_tendsto {n : ℕ} (u : H1Vector n)
    (W : Configuration n → ℝ) (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2)) :
    Tendsto (fun k : ℕ => potentialForm (fun x => min (W x) (k:ℝ)) u)
      atTop (𝓝 (potentialForm W u)) := by
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => W x*‖u.value s x‖^2)
  · intro k
    exact (hW.min measurable_const).aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
  · exact hi s
  · intro k
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (le_min (hW0 x) (Nat.cast_nonneg k)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  · filter_upwards [] with x
    apply Tendsto.congr' _ tendsto_const_nhds
    have he : ∀ᶠ k : ℕ in atTop, W x≤(k:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (W x))
    exact he.mono (fun k hk => by dsimp only; rw [min_eq_left hk])

namespace RecordedEnsemble
lemma Conserves.nonnegative_observable {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (W : Configuration n → ℝ)
    (hW : Measurable W) (hW0 : ∀ x,0≤W x)
    (hi : ∀ s,Integrable (fun x => W x*‖u.value s x‖^2))
    (hTi : ∀ p s,Integrable (fun x => W (reindexConfiguration (T.labels p) x)*‖(T.vector p).value s x‖^2)) :
    (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))=potentialForm W u := by
  have hleft : Tendsto (fun k : ℕ => ∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p)) atTop
      (𝓝 (∑ p,potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))) := by
    apply tendsto_finsetSum
    intro p _
    exact potentialForm_min_tendsto (T.vector p) _
      (hW.comp (reindexConfiguration_measurePreserving _).measurable) (fun x => hW0 _) (hTi p)
  have he (k : ℕ) : (∑ p,potentialForm
      ((fun x => min (W x) (k:ℝ)) ∘ reindexConfiguration (T.labels p)) (T.vector p))=
      potentialForm (fun x => min (W x) (k:ℝ)) u := by
    apply hT _ (hW.min measurable_const)
    exact ⟨k,fun x => by rw [abs_of_nonneg (le_min (hW0 x) (Nat.cast_nonneg k))]; exact min_le_right _ _⟩
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft (potentialForm_min_tendsto u W hW hW0 hi)
end RecordedEnsemble

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NearLpCoulomb
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma coulombKernel_fiveHalves_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Space => coulombKernel x^(5/2:ℝ)) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp) (by norm_num)
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg _) _)]
    simp only [coulombKernel,Real.inv_rpow (norm_nonneg _),one_mul]
    rw [Real.rpow_neg (norm_nonneg _)]
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma coulombKernel_fiveHalves_ball_integral {R : ℝ} (hR : 0≤R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x^(5/2:ℝ)) =
      8*Real.pi*R^(1/2:ℝ) := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t<R then t^(-5/2:ℝ) else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x^(5/2:ℝ)) =
      ∫ x : Space, if ‖x‖<R then ‖x‖^(-5/2:ℝ) else 0 := by
    rw [←integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : ‖x‖<R
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx,coulombKernel,
        Real.inv_rpow (norm_nonneg _),Real.rpow_neg (norm_nonneg _),neg_div]
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx]
  rw [hleft,H]
  have hball : volume.real (Metric.ball (0:Space) 1)=4*Real.pi/3 := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space=3 := by simp [Space]
  simp only [hdim,hball,nsmul_eq_mul,smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ),t^(3-1)*(if t<R then t^(-5/2:ℝ) else 0))=
      ∫ t in Ioo 0 R, t^(-1/2:ℝ) := by
    calc
      _=∫ t in Ioi (0:ℝ), (Iio R).indicator (fun t : ℝ => t^(-1/2:ℝ)) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        by_cases h : t<R
        · simp only [h,ite_true,Set.indicator,mem_Iio]
          have ht' : 0<t := ht
          norm_num only
          rw [←Real.rpow_natCast t 2,←Real.rpow_add ht']
          norm_num
        · simp [Set.indicator,h]
      _=_ := by rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
        inter_comm,Ioi_inter_Iio]
  rw [hint,setIntegral_congr_set Ioo_ae_eq_Ioc,←intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -1/2))]
  norm_num
  ring

lemma translated_coulomb_power_ball_integral (y : Space) {R : ℝ} (hR : 0≤R) :
    (∫ x in Metric.ball y R, coulombKernel (y-x)^(5/2:ℝ))=8*Real.pi*R^(1/2:ℝ) := by
  have he : (Metric.ball y R).indicator (fun x => coulombKernel (y-x)^(5/2:ℝ))=
      fun x => (Metric.ball (0:Space) R).indicator (fun z => coulombKernel z^(5/2:ℝ)) (y-x) := by
    funext x
    have hh : y-x∈Metric.ball (0:Space) R ↔ x∈Metric.ball y R := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hx : x∈Metric.ball y R <;> simp [hh,hx]
  rw [←integral_indicator measurableSet_ball,he,integral_sub_left_eq_self,
    integral_indicator measurableSet_ball,coulombKernel_fiveHalves_ball_integral hR]

lemma translated_coulomb_memLp_fiveHalves (y : Space) (R : ℝ) :
    MemLp (fun x => coulombKernel (y-x)) (ENNReal.ofReal (5/2:ℝ))
      (volume.restrict (Metric.ball y R)) := by
  apply (integrable_norm_rpow_iff
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (by norm_num : ENNReal.ofReal (5/2:ℝ)≠0) (by simp)).mp
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]
  change IntegrableOn (fun x => ‖coulombKernel (y-x)‖^(5/2:ℝ)) (Metric.ball y R)
  simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
  rw [←integrable_indicator_iff measurableSet_ball]
  have he : (Metric.ball y R).indicator (fun x => coulombKernel (y-x)^(5/2:ℝ))=
      fun x => (Metric.ball (0:Space) R).indicator (fun z => coulombKernel z^(5/2:ℝ)) (y-x) := by
    funext x
    have hh : y-x∈Metric.ball (0:Space) R ↔ x∈Metric.ball y R := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hx : x∈Metric.ball y R <;> simp [hh,hx]
  rw [he]
  exact (integrable_comp_sub_left _ y).mpr
    ((coulombKernel_fiveHalves_integrableOn_ball R).integrable_indicator measurableSet_ball)

theorem near_coulomb_holder {ρ : Space → ℝ} (y : Space) {R : ℝ} (hR : 0≤R)
    (hρ : MemLp ρ (ENNReal.ofReal (5/3:ℝ)) (volume.restrict (Metric.ball y R)))
    (hp : 0≤ᵐ[volume.restrict (Metric.ball y R)] ρ) :
    (∫ x in Metric.ball y R, ρ x*coulombKernel (y-x))≤
      (∫ x in Metric.ball y R, ρ x^(5/3:ℝ))^(3/5:ℝ)*
        ((8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ)) := by
  have hc : (5/3:ℝ).HolderConjugate (5/2:ℝ) := by
    rw [Real.holderConjugate_iff]; norm_num
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg hc hp
    (Eventually.of_forall (fun x => coulombKernel_nonneg (y-x))) hρ
    (translated_coulomb_memLp_fiveHalves y R)
  rw [translated_coulomb_power_ball_integral y hR] at H
  norm_num only at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤8*Real.pi) (Real.rpow_nonneg hR _),
    ←Real.rpow_mul hR]
  norm_num

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FlatBodyDensity
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma add_power_five_thirds_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^(5/3:ℝ) ≤ 4*(a^(5/3:ℝ)+b^(5/3:ℝ)) := by
  have h2 : (2:ℝ)^(5/3:ℝ) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have h (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      (a+b)^(5/3:ℝ) ≤ 4*(a^(5/3:ℝ)+b^(5/3:ℝ)) := by
    calc
      _ ≤ (2*b)^(5/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2:ℝ)^(5/3:ℝ)*b^(5/3:ℝ) := Real.mul_rpow (by norm_num) hb
      _ ≤ 4*b^(5/3:ℝ) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hb _)
      _ ≤ _ := by nlinarith [Real.rpow_nonneg ha (5/3:ℝ)]
  rcases le_total a b with hab | hba
  · exact h a b ha hb hab
  · simpa only [add_comm] using h b a hb ha hba

lemma flatOneBodyDensity_nonneg {n : ℕ} (ψ : H1Vector (n+1)) (x : Fin 3 → ℝ) :
    0 ≤ flatOneBodyDensity ψ x :=
  Finset.sum_nonneg (fun _ _ => firstParticleDensity_nonneg _ _)

lemma flatOneBodyDensity_integrable {n : ℕ} (ψ : H1Vector (n+1)) :
    Integrable (flatOneBodyDensity ψ) volume := by
  have hs := (firstParticleDensity_integrable ψ.cubeState_full_memLp).prod_right_ae
  rw [Measure.ae_count_iff] at hs
  exact integrable_finsetSum _ (fun s _ => hs s)

lemma flatOneBodyDensity_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume ∧
    (∫ x, (flatOneBodyDensity ψ x)^(5/3:ℝ)) ≤ (32768/(3*Real.pi^2))*kinetic ψ := by
  obtain ⟨hi,hb⟩ := global_spin_density_power_bound ψ hψ hm
  have hs := hi.prod_right_ae
  rw [Measure.ae_count_iff] at hs
  let B (x : Fin 3 → ℝ) := 4*∑ s : Fin 2,
    (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x))^(5/3:ℝ)
  have hB : Integrable B volume := (integrable_finsetSum _ (fun s _ => hs s)).const_mul _
  have hle (x) : (flatOneBodyDensity ψ x)^(5/3:ℝ) ≤ B x := by
    simpa only [B, flatOneBodyDensity, Fin.sum_univ_two] using add_power_five_thirds_le
      (firstParticleDensity_nonneg (cubeState ψ) (0,x))
      (firstParticleDensity_nonneg (cubeState ψ) (1,x))
  have hd : AEStronglyMeasurable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume :=
    ((flatOneBodyDensity_integrable ψ).aemeasurable.pow_const _).aestronglyMeasurable
  have hI : Integrable (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ)) volume :=
    hB.mono' hd (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (flatOneBodyDensity_nonneg ψ x) _)]
      exact hle x))
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, B x := integral_mono hI hB hle
    _ = 4*∑ s : Fin 2, ∫ x,
        (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) (s,x))^(5/3:ℝ) := by
      simp only [B, integral_const_mul]
      rw [integral_finsetSum _ (fun s _ => hs s)]
    _ = 4*∫ sx, (firstParticleDensity (μ := spinSpaceMeasure) (cubeState ψ) sx)^(5/3:ℝ)
        ∂spinSpaceMeasure := by
      congr 1
      exact ((integral_prod _ hi).trans (integral_count _)).symm
    _ ≤ 4*((8192/(3*Real.pi^2))*kinetic ψ) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

lemma oneBodyDensity_integrable {n : ℕ} (ψ : H1Vector (n+1)) :
    Integrable (oneBodyDensity ψ) volume :=
  (PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable
    (flatOneBodyDensity_integrable ψ)

lemma oneBodyDensity_power_bound {n : ℕ} (ψ : H1Vector (n+1))
    (hψ : Antisymmetric ψ) (hm : mass ψ ≤ 1) :
    Integrable (fun x => (oneBodyDensity ψ x)^(5/3:ℝ)) volume ∧
    (∫ x, (oneBodyDensity ψ x)^(5/3:ℝ)) ≤ (32768/(3*Real.pi^2))*kinetic ψ := by
  obtain ⟨hi,hb⟩ := flatOneBodyDensity_power_bound ψ hψ hm
  refine ⟨(PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable hi, ?_⟩
  change (∫ x : Space, (flatOneBodyDensity ψ ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x))^(5/3:ℝ)) ≤ _
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun x => (flatOneBodyDensity ψ x)^(5/3:ℝ))]
  exact hb

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

theorem integrable_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Position × Configuration N => f (Fin.cons p.1 p.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := (he.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  simpa [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem integral_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    (∫ x : Position, ∫ y : Configuration N, f (Fin.cons x y)) = ∫ z, f z := by
  rw [← integral_prod _ (integrable_cons hf)]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := he.integral_comp' f
  simpa [MeasureTheory.Measure.volume_eq_prod, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem piCongrLeft_perm {ι α : Type*} (p : Equiv.Perm ι) (x : ι → α) :
    Equiv.piCongrLeft (fun _ : ι => α) p.symm x = x ∘ p := by
  funext i
  simp [Equiv.piCongrLeft_apply]

theorem configurationDensity_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) :
    (fun x : Configuration n => configurationDensity ψ (x ∘ p)) =ᵐ[volume]
      configurationDensity ψ := by
  have hsign : ‖(((Equiv.Perm.sign p : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> simp [hp]
  have ha : ∀ᵐ x : Configuration n ∂volume, ∀ σ : Spins n,
      ψ (σ ∘ p) (x ∘ p) = (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x :=
    (ae_all_iff).mpr (hψ p)
  filter_upwards [ha] with x hx
  unfold configurationDensity
  have hsum := (Equiv.piCongrLeft (fun _ : Fin n => Fin 2) p.symm).sum_comp
    (fun σ : Spins n => ‖ψ σ (x ∘ p)‖ ^ 2)
  have hh : (∑ σ : Spins n, ‖ψ (σ ∘ p) (x ∘ p)‖ ^ 2) =
      ∑ σ : Spins n, ‖ψ σ (x ∘ p)‖ ^ 2 := by
    simpa only [piCongrLeft_perm] using hsum
  rw [← hh]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hx σ, norm_mul, hsign, one_mul]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_UniformGroundStateCountControl
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem rawExpectation_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) (F : Configuration n → ℝ) :
    rawExpectation ψ (fun x => F (x ∘ p)) = rawExpectation ψ F := by
  unfold rawExpectation
  calc
    (∫ x, F (x ∘ p) * configurationDensity ψ x) =
        ∫ x, F (x ∘ p) * configurationDensity ψ (x ∘ p) := by
      apply integral_congr_ae
      filter_upwards [configurationDensity_perm hψ p] with x hx
      rw [hx]
    _ = ∫ x, F x * configurationDensity ψ x := by
      have hi := (volume_measurePreserving_piCongrLeft
        (fun _ : Fin n => Position) p.symm).integral_comp'
        (fun x => F x * configurationDensity ψ x)
      simpa only [MeasurableEquiv.coe_piCongrLeft, piCongrLeft_perm] using hi

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma flattenConfiguration_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).toHomeomorph.toMeasurableEquiv :=
  (flattenConfiguration_symm_measurePreserving n).symm

lemma fromH1_weak {n : ℕ} (ψ : Coulomb.H1Vector n) :
    HasWeakGradient (fromH1Wave ψ) (fromH1Gradient ψ) := by
  intro s i a φ hφ hc
  have H := weakDirectional_pullback (flattenConfiguration n)
    (flattenConfiguration_measurePreserving n) (ψ.weak_partial s (i,a))
    (flattenConfiguration_coordinateDirection i a) φ hφ hc
  simpa only [fromH1Wave,fromH1Gradient,mul_comm] using H

lemma fromH1_domain {n : ℕ} (ψ : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric ψ) :
    FormDomain (fromH1Wave ψ) (fromH1Gradient ψ) := by
  refine ⟨?_, fromH1_weak ψ, ?_, ?_, ?_, ?_⟩
  · intro p s
    exact (flattenConfiguration_measurePreserving n).quasiMeasurePreserving.ae (ha p s)
  · intro s
    exact (ψ.value_L2 s).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i a
    exact (ψ.partial_L2 s (i,a)).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i
    have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0:ℝ)<1)).1
    change Integrable (fun x : Configuration n => ‖x i-0‖⁻¹*‖fromH1Wave ψ s x‖^2) at H
    simpa only [sub_zero] using H
  · intro s i j hij
    exact (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0:ℝ)<1)).1

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_PhysicalLTBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma firstParticleDensity_physical_slice {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (s : Fin 2) (x : Position)
    (hi : ∀ σ : Spins N,Integrable (fun y : Configuration N =>
      ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2)) :
    Coulomb.firstParticleDensity (μ := Coulomb.spinSpaceMeasure) (Coulomb.cubeState u)
      (s,WithLp.ofLp x) = (N+1:ℝ)*∑ σ : Spins N,∫ y : Configuration N,
        ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2 := by
  unfold Coulomb.firstParticleDensity
  simp only [Nat.cast_add,Nat.cast_one]
  congr 1
  let F (σ : Coulomb.Spins N) (z : Coulomb.Configuration N) : ℝ :=
    ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x ((flattenConfiguration N).symm z))‖^2
  have hF (σ) : Integrable (F σ) :=
    (flattenConfiguration_symm_measurePreserving N).integrable_comp_of_integrable (hi σ)
  calc
    _=∫ z,F ((Coulomb.spinCubeEquiv N) z).1
        (WithLp.toLp 2 ((Coulomb.spinCubeEquiv N) z).2)
        ∂(Measure.pi fun _ : Fin N => Coulomb.spinSpaceMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 2
      unfold Coulomb.firstFiber Coulomb.cubeState fromH1Wave
      congr 1
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      · ext ⟨i,a⟩
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    _=∑ σ,∫ z,F σ z := Coulomb.spinConfiguration_integral F hF
    _=_ := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (flattenConfiguration_symm_measurePreserving N).integral_comp'
        (fun y : Configuration N => ‖fromH1Wave u (Fin.cons s σ) (Fin.cons x y)‖^2)

theorem density_fromH1_eq_oneBodyDensity {N : ℕ} (u : Coulomb.H1Vector (N+1)) :
    density (fromH1Wave u)=ᵐ[volume] Coulomb.oneBodyDensity u := by
  have hL (σ : Spins (N+1)) : Integrable (fun z : Configuration (N+1) => ‖fromH1Wave u σ z‖^2) :=
    ((u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving (N+1))).norm.integrable_sq
  have hi : ∀ᵐ x : Position,∀ σ : Spins (N+1),Integrable
      (fun y : Configuration N => ‖fromH1Wave u σ (Fin.cons x y)‖^2) := by
    rw [ae_all_iff]
    intro σ
    exact (integrable_cons (hL σ)).prod_right_ae
  filter_upwards [hi] with x hx
  unfold Coulomb.oneBodyDensity Coulomb.flatOneBodyDensity
  simp_rw [firstParticleDensity_physical_slice u _ x (fun σ => hx _)]
  rw [←Finset.mul_sum]
  unfold density
  congr 1
  let e : Spins (N+1) ≃ (Fin 2 × Spins N) :=
    { toFun := fun σ => (σ 0,Fin.tail σ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := fun σ => Fin.cons_self_tail σ
      right_inv := fun p => by cases p; rfl }
  calc
    _=∑ p : Fin 2 × Spins N,∫ y : Configuration N,
        ‖fromH1Wave u (Fin.cons p.1 p.2) (Fin.cons x y)‖^2 := by
      apply Fintype.sum_equiv e
      intro σ
      change (∫ y : Configuration N,‖fromH1Wave u σ (Fin.cons x y)‖^2)=
        ∫ y : Configuration N,‖fromH1Wave u (Fin.cons (σ 0) (Fin.tail σ)) (Fin.cons x y)‖^2
      rw [Fin.cons_self_tail]
    _=_ := Fintype.sum_prod_type _

theorem physical_density_power_bound {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (hu : Coulomb.Antisymmetric u) (hm : Coulomb.mass u≤1) :
    Integrable (fun x => (density (fromH1Wave u) x)^(5/3:ℝ)) ∧
    (∫ x,(density (fromH1Wave u) x)^(5/3:ℝ))≤(32768/(3*Real.pi^2))*Coulomb.kinetic u := by
  have he := (density_fromH1_eq_oneBodyDensity u).fun_comp (fun t : ℝ => t^(5/3:ℝ))
  obtain ⟨hi,hb⟩ := Coulomb.oneBodyDensity_power_bound u hu hm
  exact ⟨hi.congr he.symm,(integral_congr_ae he).trans_le hb⟩
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalDensityWeighted
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

theorem density_weight_eq_first_site {N : ℕ} (ψ : Wavefunction (N+1))
    (W : Position → ℝ)
    (hi : ∀ σ,Integrable (fun x : Configuration (N+1) => W (x 0)*‖ψ σ x‖^2)) :
    (∫ z,W z*density ψ z)=(N+1:ℝ)*rawExpectation ψ (fun x => W (x 0)) := by
  have hw (σ : Spins (N+1)) := (integrable_cons (hi σ)).integral_prod_left
  have he (σ : Spins (N+1)) :
      (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2))=
      fun z => ∫ x : Configuration N,W z*‖ψ σ (Fin.cons z x)‖^2 := by
    funext z
    rw [integral_const_mul]
  have hw' (σ : Spins (N+1)) : Integrable (fun z => W z*(∫ x : Configuration N,‖ψ σ (Fin.cons z x)‖^2)) := by
    rw [he]
    simpa only [Fin.cons_zero] using hw σ
  unfold density rawExpectation configurationDensity
  simp_rw [mul_left_comm (W _) (N+1:ℝ)]
  rw [integral_const_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => hw' σ),
    integral_finsetSum _ (fun σ _ => hi σ)]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [he σ]
  simpa only [Fin.cons_zero] using integral_cons (hi σ)

theorem rawExpectation_oneBody_eq_density {N : ℕ} {ψ : Wavefunction (N+1)}
    (ha : IsAntisymmetric ψ) (W : Position → ℝ)
    (hi : ∀ σ i,Integrable (fun x : Configuration (N+1) => W (x i)*‖ψ σ x‖^2)) :
    rawExpectation ψ (fun x => ∑ i : Fin (N+1),W (x i))=∫ z,W z*density ψ z := by
  have hii (i : Fin (N+1)) : Integrable (fun x => W (x i)*configurationDensity ψ x) := by
    simp only [configurationDensity,Finset.mul_sum]
    exact integrable_finsetSum _ (fun σ _ => hi σ i)
  calc
    _=∑ i : Fin (N+1),rawExpectation ψ (fun x => W (x i)) := by
      unfold rawExpectation
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum _ (fun i _ => hii i)
    _=∑ _i : Fin (N+1),rawExpectation ψ (fun x => W (x 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Function.comp_apply,Equiv.swap_apply_left] using
        rawExpectation_perm ha (Equiv.swap 0 i) (fun x => W (x 0))
    _=_ := by rw [density_weight_eq_first_site ψ W (fun σ => hi σ 0)]; simp

lemma fromH1_coulomb_weight_integrable {n : ℕ} (u : Coulomb.H1Vector n)
    (y : Position) (σ : Spins n) (i : Fin n) :
    Integrable (fun x : Configuration n => coulombKernel (y-x i)*‖fromH1Wave u σ x‖^2) := by
  have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
    (u.nuclear_coulomb_integrable_bound σ i y (by norm_num : (0:ℝ)<1)).1
  change Integrable (fun x : Configuration n => Coulomb.coulombKernel (x i-y)*‖fromH1Wave u σ x‖^2) at H
  simpa only [coulombKernel,Coulomb.coulombKernel,norm_sub_rev] using H

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicNear
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb

lemma nearWeight_nonneg (y : Space) (R : ℝ) (z : Space) : 0≤nearWeight y R z := by
  unfold nearWeight
  exact Set.indicator_nonneg (fun z _ => coulombKernel_nonneg _) z
lemma nearWeight_measurable (y : Space) (R : ℝ) : Measurable (nearWeight y R) :=
  (coulombKernel_measurable.comp (measurable_const.sub measurable_id)).indicator measurableSet_ball
lemma nearPotential_nonneg {n : ℕ} (y : Space) (R : ℝ) (x : Configuration n) : 0≤nearPotential y R x :=
  Finset.sum_nonneg (fun index _ => nearWeight_nonneg y R (position x index))
lemma nearPotential_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ) (s : Spins n) :
    Integrable (fun x => nearPotential y R x*‖u.value s x‖^2) := by
  have hi (i : Fin n) : Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
    have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
    have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
      simpa only [coulombKernel,norm_sub_rev] using H
    have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
      (continuous_position i).measurable)
    apply hh.congr
    filter_upwards [] with x
    by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]
  simpa only [nearPotential,Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi i)

lemma nearPotential_physical {N : ℕ} (u : H1Vector (N+1)) (hu : Antisymmetric u)
    (y : Space) (R : ℝ) : potentialForm (nearPotential y R) u=
      ∫ z in Metric.ball y R,NeutralAtom.density (NeutralAtom.fromH1Wave u) z*coulombKernel (y-z) := by
  have hd := NeutralAtom.fromH1_domain u hu
  have hi (s : NeutralAtom.Spins (N+1)) (i : Fin (N+1)) :
      Integrable (fun x : NeutralAtom.Configuration (N+1) => nearWeight y R (x i)*‖NeutralAtom.fromH1Wave u s x‖^2) := by
    have H := (NeutralAtom.fromH1_coulomb_weight_integrable u y s i).indicator
      ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage (measurable_pi_apply i))
    apply H.congr
    filter_upwards [] with x
    by_cases hx : x i∈Metric.ball y R <;> simp [nearWeight,hx,NeutralAtom.coulombKernel,coulombKernel]
  have he : potentialForm (nearPotential y R) u=
      NeutralAtom.rawExpectation (NeutralAtom.fromH1Wave u) (fun x => ∑ i,nearWeight y R (x i)) := by
    unfold NeutralAtom.rawExpectation NeutralAtom.configurationDensity potentialForm
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun s _ => by
      simpa only [Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hi s i))]
    apply Finset.sum_congr rfl
    intro s _
    exact ((NeutralAtom.flattenConfiguration_measurePreserving (N+1)).integral_comp'
      (fun x => nearPotential y R x*‖u.value s x‖^2)).symm
  rw [he,NeutralAtom.rawExpectation_oneBody_eq_density hd.1 _ hi,←integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z∈Metric.ball y R <;> simp [nearWeight,hz,mul_comm]

lemma fermionicNearConstant_nonneg : 0≤fermionicNearConstant := by unfold fermionicNearConstant; positivity

lemma nearPotential_normalized {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u)
    (hm : mass u≤1) (y : Space) {R : ℝ} (hR : 0≤R) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*kinetic u^(3/5:ℝ)*R^(1/5:ℝ) := by
  cases n with
  | zero =>
    simp only [potentialForm,nearPotential,Finset.univ_eq_empty,Finset.sum_empty,zero_mul,integral_zero,Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg (kinetic_nonneg u) _)) (Real.rpow_nonneg hR _)
  | succ N =>
    let ρ := NeutralAtom.density (NeutralAtom.fromH1Wave u)
    have hρ0 (z) : 0≤ρ z := by
      unfold ρ NeutralAtom.density
      positivity
    obtain ⟨hp,hb⟩ := NeutralAtom.physical_density_power_bound u hu hm
    have hint : Integrable ρ := (oneBodyDensity_integrable u).congr
      (NeutralAtom.density_fromH1_eq_oneBodyDensity u).symm
    have hLp : MemLp ρ (ENNReal.ofReal (5/3:ℝ)) volume := by
      apply (integrable_norm_rpow_iff hint.aestronglyMeasurable (by norm_num) (by simp)).mp
      simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/3),Real.norm_of_nonneg (hρ0 _)] using hp
    have hlocal := near_coulomb_holder y hR (hLp.restrict _) (Eventually.of_forall hρ0)
    have hmass : (∫ z in Metric.ball y R,ρ z^(5/3:ℝ))≤∫ z,ρ z^(5/3:ℝ) :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun z => Real.rpow_nonneg (hρ0 z) _)) hp
    rw [nearPotential_physical u hu y R]
    calc
      _≤_ := hlocal
      _≤((32768/(3*Real.pi^2))*kinetic u)^(3/5:ℝ)*((8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow (integral_nonneg (fun z => Real.rpow_nonneg (hρ0 z) _))
          (hmass.trans hb) (by norm_num)
      _=_ := by
        rw [Real.mul_rpow (by positivity : (0:ℝ)≤32768/(3*Real.pi^2)) (kinetic_nonneg u)]
        unfold fermionicNearConstant
        ring

lemma rpow_three_fifths_linear {x B : ℝ} (hx : 0≤x) (hB : 0<B) :
    x^(3/5:ℝ)≤B^(-2/5:ℝ)*x+B^(3/5:ℝ) := by
  rcases le_total x B with h|h
  · exact (Real.rpow_le_rpow hx h (by norm_num)).trans (le_add_of_nonneg_left (by positivity))
  · have hx' : 0<x := hB.trans_le h
    have he : x^(3/5:ℝ)=x^(-2/5:ℝ)*x := by
      calc
        _=x^((-2/5)+1:ℝ) := by norm_num
        _=x^(-2/5:ℝ)*x^(1:ℝ) := Real.rpow_add hx' _ _
        _=_ := by rw [Real.rpow_one]
    rw [he]
    have hp : x^(-2/5:ℝ)≤B^(-2/5:ℝ) := Real.rpow_le_rpow_of_nonpos hB h (by norm_num)
    exact (mul_le_mul_of_nonneg_right hp hx).trans (le_add_of_nonneg_right (by positivity))

theorem nearPotential_linear {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u)
    (y : Space) {R B : ℝ} (hR : 0≤R) (hB : 0<B) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*kinetic u+B^(3/5:ℝ)*mass u) := by
  by_cases hz : mass u=0
  · rw [potentialForm_eq_zero_of_mass_zero _ u hz,kinetic_eq_zero_of_mass_zero u hz,hz]
    simp
  have hm : 0 < mass u := lt_of_le_of_ne (mass_nonneg u) (Ne.symm hz)
  have hn := nearPotential_normalized u.normalized hu.normalized (mass_normalized u hm).le y hR
  have hr := rpow_three_fifths_linear (kinetic_nonneg u.normalized) hB
  have hc : 0≤fermionicNearConstant*R^(1/5:ℝ) := mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg hR _)
  have hn' : potentialForm (nearPotential y R) u.normalized≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*kinetic u.normalized+B^(3/5:ℝ)) := by
    calc
      _≤(fermionicNearConstant*R^(1/5:ℝ))*kinetic u.normalized^(3/5:ℝ) := by nlinarith [hn]
      _≤_ := mul_le_mul_of_nonneg_left hr hc
  have H := mul_le_mul_of_nonneg_left hn' hm.le
  rw [potentialForm_normalized_weight] at H
  calc
    _≤_ := H
    _=_ := by
      rw [mul_left_comm (mass u),mul_add,mul_left_comm (mass u) (B^(-2/5:ℝ)),kinetic_normalized_weight]
      ring
end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace Coulomb
lemma nearWeight_site_integrable {n : ℕ} (u : H1Vector n) (y : Space) (R : ℝ)
    (s : Spins n) (i : Fin n) :
    Integrable (fun x => nearWeight y R (position x i)*‖u.value s x‖^2) := by
  have H := (u.nuclear_coulomb_integrable_bound s i y (by norm_num : (0:ℝ)<1)).1
  have hc : Integrable (fun x => coulombKernel (y-position x i)*‖u.value s x‖^2) := by
    simpa only [coulombKernel,norm_sub_rev] using H
  have hh := hc.indicator ((measurableSet_ball : MeasurableSet (Metric.ball y R)).preimage
    (continuous_position i).measurable)
  apply hh.congr
  filter_upwards [] with x
  by_cases hx : position x i∈Metric.ball y R <;> simp [nearWeight,hx]

lemma nearPotential_outer_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (R : ℝ)
    (s : Spins (m+k)) :
    Integrable (fun x => nearPotential y R ((joinConfiguration m k).symm x).1*‖u.value s x‖^2) := by
  simp only [nearPotential,position_split_left,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ => nearWeight_site_integrable u y R s (Fin.castAdd k i))

theorem outer_nearPotential_linear {m k : ℕ} (u : H1Vector (m+k))
    (hu : PartlyAntisymmetric u (outIndexSet m k))
    (y : Space) {R B : ℝ} (hR : 0≤R) (hB : 0<B) :
    potentialForm (fun x => nearPotential y R ((joinConfiguration m k).symm x).1) u≤
      fermionicNearConstant*R^(1/5:ℝ)*(B^(-2/5:ℝ)*outerKinetic u+B^(3/5:ℝ)*mass u) := by
  let C := fermionicNearConstant*R^(1/5:ℝ)
  have hi (s : Spins (m+k)) : Integrable (fun x =>
      nearPotential y R ((outerJoinConfiguration k m).symm x).2*‖u.value s x‖^2) :=
    nearPotential_outer_integrable u y R s
  have H (s : Spins k) :
      (∫ x,potentialForm (nearPotential y R) (u.outerSlice s x))≤
        C*(B^(-2/5:ℝ)*(∫ x,kinetic (u.outerSlice s x))+B^(3/5:ℝ)*(∫ x,mass (u.outerSlice s x))) := by
    have hk := (kinetic_outerSlice_integrable u s).const_mul (B^(-2/5:ℝ))
    have hm := (mass_outerSlice_integrable u s).const_mul (B^(3/5:ℝ))
    have HA := u.outerSlice_antisymmetric s (hu.outer_symmetry s)
    have HH := integral_mono_ae (potentialForm_outerSlice_integrable u s _ (fun t => hi (outerAppend s t)))
      ((hk.add hm).const_mul C) (HA.mono (fun x hx => nearPotential_linear (u.outerSlice s x) hx y hR hB))
    simpa only [Pi.add_apply,integral_const_mul,integral_add hk hm] using HH
  have HH := Finset.sum_le_sum (fun (s : Spins k) (_ : s∈Finset.univ) => H s)
  rw [integral_potentialForm_outerSlice u _ hi] at HH
  simp only [←Finset.mul_sum,Finset.sum_add_distrib] at HH
  rw [integral_mass_outerSlice,integral_kinetic_outerSlice] at HH
  exact HH

lemma supported_core_nearPotential {m k : ℕ} (u : H1Vector (m+k)) (y : Space) {R t : ℝ}
    (hRt : R≤t) (hs : PartlySupported u (coreIndexSet m k) {z | t≤‖z-y‖}) :
    potentialForm (nearPotential y R) u=
      potentialForm (fun x => nearPotential y R ((joinConfiguration m k).symm x).1) u := by
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [hs s] with x hx
  by_cases hz : u.value s x=0
  · simp [hz]
  have hcore (i : Fin k) : nearWeight y R (position x (Fin.natAdd m i))=0 := by
    have hout : position x (Fin.natAdd m i)∉Metric.ball y R := by
      intro hi
      have hi' : ‖position x (Fin.natAdd m i)-y‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hi
      exact hz (hx _ ⟨i,rfl⟩ (not_le.mpr (hi'.trans_le hRt)))
    exact Set.indicator_of_notMem hout _
  simp only [nearPotential,Fin.sum_univ_add,position_split_left,hcore,Finset.sum_const_zero,add_zero]

lemma nearPotential_reindex {m n : ℕ} (e : Fin m ≃ Fin n) (y : Space) (R : ℝ)
    (x : Configuration m) : nearPotential y R (reindexConfiguration e x)=nearPotential y R x := by
  unfold nearPotential
  exact (Equiv.sum_comp e (fun i => nearWeight y R (position (reindexConfiguration e x) i))).symm.trans
    (Finset.sum_congr rfl (fun i _ => by rw [position_reindex]))
lemma nearPotential_measurable {n : ℕ} (y : Space) (R : ℝ) : Measurable (nearPotential (n := n) y R) :=
  Finset.measurable_sum _ (fun i _ => (nearWeight_measurable y R).comp (continuous_position i).measurable)

lemma RecordedEnsemble.Conserves.nearPotential {n : ℕ} {T : RecordedEnsemble n}
    {u : H1Vector n} (hT : T.Conserves u) (y : Space) (R : ℝ) :
    (∑ p,potentialForm (Coulomb.nearPotential y R) (T.vector p))=potentialForm (Coulomb.nearPotential y R) u := by
  have H := hT.nonnegative_observable (Coulomb.nearPotential y R) (nearPotential_measurable y R)
    (nearPotential_nonneg y R) (nearPotential_integrable u y R)
    (fun p s => by simpa only [nearPotential_reindex] using nearPotential_integrable (T.vector p) y R s)
  simpa only [Function.comp_def,nearPotential_reindex] using H

theorem RecordedEnsemble.nearPotential_le {n : ℕ} (T : RecordedEnsemble n) (u : H1Vector n)
    (hc : T.Conserves u) (ho : T.OutFermionic) (y : Space) {R t B : ℝ}
    (hR : 0≤R) (hRt : R≤t) (hB : 0<B)
    (hs : T.CoreSupported {z | t≤‖z-y‖}) :
    potentialForm (nearPotential y R) u≤fermionicNearConstant*R^(1/5:ℝ)*
      (B^(-2/5:ℝ)*(∑ p,outerKinetic (T.vector p))+B^(3/5:ℝ)*T.totalMass) := by
  rw [←hc.nearPotential y R]
  have H := Finset.sum_le_sum (fun (p : T.index) (_ : p∈Finset.univ) =>
    (supported_core_nearPotential (T.vector p) y hRt (hs p)).le.trans
      (outer_nearPotential_linear (T.vector p) (ho p) y hR hB))
  simpa only [←Finset.mul_sum,Finset.sum_add_distrib,RecordedEnsemble.totalMass] using H
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_AtomicOutKinetic
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma slice_core_form_ge_baseline {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    E*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u E]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) E] using (mass_coreSlice_integrable u s).const_mul E)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hE.trans
      (unrestrictedFormBottom_le_trial S _ hx.normalized (mass_normalized _ hp)))

theorem atomic_outerKinetic_le {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {y : Space} (hy : y≠0)
    (hs : PartlySupported u (outIndexSet m k) (Metric.closedBall y (80*atomicCellScale y)))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    outerKinetic u≤form S u-E*mass u+
      (atomicCellScale y/2)*sliceExpectation u (fun s x => (atomicPatchCap S (u.coreSlice s x).normalized x y)^2)+
      (m:ℝ)^2/(2*atomicCellScale y)*mass u := by
  let a := atomicCellScale y
  have hapos : 0<a := atomicCellScale_pos hy
  have hbase := slice_core_form_ge_baseline S u ha hE
  have hcost : -((a/2)*sliceExpectation u (fun s x => (atomicPatchCap S (u.coreSlice s x).normalized x y)^2)+
      (m:ℝ)^2/(2*a)*mass u)≤
      sliceExpectation u (fun s x => pairPotential x-∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i)) := by
    rw [←sliceExpectation_number u ((m:ℝ)^2/(2*a))]
    unfold sliceExpectation
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro s _
    rw [←integral_const_mul,←integral_add ((atomicPatchCap_weight_integrable S hatom u s hy).const_mul (a/2))
      ((mass_coreSlice_integrable u s).mul_const _),←integral_neg]
    apply integral_mono_ae
      (((atomicPatchCap_weight_integrable S hatom u s hy).const_mul (a/2)).add
        ((mass_coreSlice_integrable u s).mul_const _)).neg
      (conditionalOutCost_weight_integrable S u s)
    filter_upwards [hs.recorded_positions s] with x hx
    by_cases hz : mass (u.coreSlice s x)=0
    · simp [hz]
    · have hfield : (∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i))≤
          (m:ℝ)*atomicPatchCap S (u.coreSlice s x).normalized x y := by
        calc
          _≤∑ _i : Fin m,atomicPatchCap S (u.coreSlice s x).normalized x y := by
            apply Finset.sum_le_sum
            intro i _
            apply coreField_le_atomicPatchCap S hatom _ x hy
            simpa only [Metric.mem_closedBall,dist_eq_norm] using hx hz i
          _=_ := by simp
      have hsq := sq_nonneg (a*atomicPatchCap S (u.coreSlice s x).normalized x y-(m:ℝ))
      have hyoung : (m:ℝ)*atomicPatchCap S (u.coreSlice s x).normalized x y≤
          (a/2)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2+(m:ℝ)^2/(2*a) := by
        apply (mul_le_mul_iff_right₀ (show 0<2*a by positivity)).mp
        have he : (m:ℝ)^2/(2*a)*(2*a)=(m:ℝ)^2 := div_mul_cancel₀ _ (by positivity)
        nlinarith
      have hh := mul_le_mul_of_nonneg_left (show -((a/2)*(atomicPatchCap S (u.coreSlice s x).normalized x y)^2+
          (m:ℝ)^2/(2*a))≤pairPotential x-∑ i : Fin m,coreScreenedField S (u.coreSlice s x).normalized (position x i) by
          have hp : 0≤pairPotential x := by
            unfold pairPotential
            exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
              split_ifs <;> simp [coulombKernel]))
          linarith) (mass_nonneg (u.coreSlice s x))
      dsimp only [Pi.add_apply,Pi.neg_apply,Pi.mul_apply]
      nlinarith
  have hid := form_eq_conditionalOutCost S u
  unfold conditionalOutCost at hid
  change outerKinetic u≤form S u-E*mass u+(a/2)*_+(m:ℝ)^2/(2*a)*mass u
  linarith

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AtomicSmallPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma screenMass_ge_inverse_cube (δ : ℝ) {a : ℝ} (ha : 0<a) :
    a^(-3:ℝ) ≤ screenMass δ a := by
  rw [Real.rpow_neg ha.le,Real.rpow_ofNat]
  unfold screenMass screenBaseMass
  linarith [le_max_left ((a^3)⁻¹) (1:ℝ), Real.sqrt_nonneg (δ*a)]

lemma source_patch_scale_condition {a P δ : ℝ} (ha : 0<a) (ha1 : a≤1) (hP : 1≤P) :
    a≤(a^(6/5:ℝ))^2*Real.sqrt P*screenMass δ a := by
  have hb : 0≤(a^(6/5:ℝ))^2 := sq_nonneg _
  have hm := screenMass_ge_inverse_cube δ ha
  have hs := Real.one_le_sqrt.mpr hP
  have he : (a^(6/5:ℝ))^2*a^(-3:ℝ)=a^(-3/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_add ha]
    norm_num
  calc
    a = a^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ a^(-3/5:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
    _ = (a^(6/5:ℝ))^2*1*a^(-3:ℝ) := by rw [mul_one,he]
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs hb) hm
      (Real.rpow_nonneg ha.le _) (mul_nonneg hb (Real.sqrt_nonneg _))

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_AtomicPhysicalKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

theorem RecordedEnsemble.atomic_outerKinetic_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (T : RecordedEnsemble n) (ha : T.CoreFermionic)
    {y : Space} (hy : y≠0) (hs : T.OutSupported (Metric.closedBall y (80*atomicCellScale y)))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    (∑ p,outerKinetic (T.vector p))≤T.totalForm S-E*T.totalMass+
      (atomicCellScale y/2)*(∑ p,sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2))+
      (∑ p,(T.out p:ℝ)^2*mass (T.vector p))/(2*atomicCellScale y) := by
  have H := Finset.sum_le_sum (fun (p : T.index) (_ : p∈Finset.univ) =>
    Coulomb.atomic_outerKinetic_le S hatom (T.vector p) (ha p).coreSlice hy (hs p) hE)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at H
  apply H.trans_eq
  unfold totalForm totalMass
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem exists_atomic_physical_kinetic {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      (∑ p,outerKinetic (T.ensemble.vector p))≤
        δ+thinReserveFactor*(Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)/b^2)+
          (atomicPhysicalCapConstant+atomicPatchCountFactor)*screenCountParameter ψ δ*
            (screenMass δ (atomicCellScale y))^2/(2*atomicCellScale y) := by
  let a := atomicCellScale y
  let P := screenCountParameter ψ δ
  let m := screenMass δ a
  have ha : 0<a := atomicCellScale_pos hy
  have hP : 0≤P := le_trans zero_le_one (screenCountParameter_ge_one ψ δ)
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hD,hN,hraw⟩ :=
    exists_atomic_thin_screened_sharp S hatom ψ hψ hm hE hstate hδ hy hb hsmall hcond
  let Q := ∑ p,sliceExpectation (T.ensemble.vector p) (fun s x => (atomicPatchCap S ((T.ensemble.vector p).coreSlice s x).normalized x y)^2)
  let N := ∑ p,(T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p)
  have hwidth : t+b≤80*a := by dsimp only [a] at *; linarith [ht.2]
  have hQ : Q≤atomicPhysicalCapConstant*P*m^2/a^2 := by
    have HQ := atomicPatchCap_ensemble_square S hatom T.ensemble hy
      (H := (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2)
      (fun v hv => (Real.sqrt_le_iff.mp (hraw v hv)).2)
    change Q≤_ at HQ
    calc
      Q≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+8*N/(9*a^2) := HQ
      _≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+
        8*(atomicPatchCountFactor*P*m^2)/(9*a^2) := add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity))
      _=atomicPhysicalCapConstant*P*m^2/a^2 := by
        dsimp only [atomicPhysicalCapConstant,screenFieldUnit,m]
        simp only [mul_pow,div_pow,Real.sq_sqrt hP]
        ring
  have hs : T.ensemble.OutSupported (Metric.closedBall y (80*a)) := by
    intro p s
    filter_upwards [hos p s] with x hx
    intro i hi hn
    exact hx i hi (fun hh => hn (Metric.closedBall_subset_closedBall hwidth hh))
  have HK := RecordedEnsemble.atomic_outerKinetic_le S hatom T.ensemble T.fermionic hy hs hE
  rw [T.mass_eq,hm,mul_one] at HK
  have hB := thinIMS_sharp_budget ψ hm hδ hP
    (fun z hz => screenCountParameter_controls ψ hm δ hz) hy hb hwidth
  have hq := mul_le_mul_of_nonneg_left hQ (show 0≤a/2 by positivity)
  have hn := div_le_div_of_nonneg_right hN (show 0≤2*a by positivity)
  refine ⟨t,ht,T,hEt,ho,hcs,hos,?_⟩
  change _≤δ+thinReserveFactor*(Real.sqrt P*m/b^2)+(atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a)
  have hident : (a/2)*(atomicPhysicalCapConstant*P*m^2/a^2)+atomicPatchCountFactor*P*m^2/(2*a)=
      (atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a) := by field_simp
  change _≤T.ensemble.totalForm S-E+(a/2)*Q+N/(2*a) at HK
  dsimp only [m,P,a] at hq hn hident hB HK ⊢
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma atomicKineticFormula_small {δ P a : ℝ} (hδ : 0≤δ)
    (hP : 0≤P) (hPP : P≤atomicCountConstant) (ha : 0<a) (ha1 : a≤1)
    (hd : δ≤a^(-349/50:ℝ)) :
    atomicKineticFormula δ P (screenMass δ a) a (a^(6/5:ℝ))≤atomicKineticConstant*a^(-7:ℝ) := by
  have hsmall : δ*a^7≤1 := by
    calc
      δ*a^7≤a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _=a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _≤1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm : screenMass δ a≤2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using
      NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hmn := (screenMass_pos δ a).le
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hT := thinReserveFactor_nonneg
  have hC := hP.trans hPP
  have hbound : atomicKineticFormula δ P (screenMass δ a) a (a^(6/5:ℝ))≤
      atomicKineticFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) := by
    unfold atomicKineticFormula
    gcongr
  have he : atomicKineticFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ))=
      a^(-349/50:ℝ)+(2*thinReserveFactor*Real.sqrt atomicCountConstant)*a^(-27/5:ℝ)+
        (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-7:ℝ) := by
    have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
      rw [mul_pow,←Real.rpow_mul_natCast ha.le]; norm_num
    have hb2 : (a^(6/5:ℝ))^2=a^(12/5:ℝ) := by rw [←Real.rpow_mul_natCast ha.le]; norm_num
    unfold atomicKineticFormula
    rw [hm2,hb2]
    have h1 : Real.sqrt atomicCountConstant*(2*a^(-3:ℝ))/a^(12/5:ℝ)=
        (2*Real.sqrt atomicCountConstant)*a^(-27/5:ℝ) := by
      rw [show Real.sqrt atomicCountConstant*(2*a^(-3:ℝ))=(2*Real.sqrt atomicCountConstant)*a^(-3:ℝ) by ring,
        div_rpow_monomial ha]
      norm_num
    rw [h1]
    have h2 : (atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant*(4*a^(-6:ℝ))/(2*a)=
        (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-7:ℝ) := by
      calc
        _=((2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-6:ℝ))/a := by ring
        _=_ := by
          have H := div_rpow_monomial ha (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant) (-6) 1
          simp only [Real.rpow_one] at H
          convert H using 1
          all_goals try with_reducible_and_instances rfl
          norm_num
    rw [h2]
    ring
  rw [he] at hbound
  have h1 : a^(-349/50:ℝ)≤a^(-7:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
  have h2 : a^(-27/5:ℝ)≤a^(-7:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0≤2*thinReserveFactor*Real.sqrt atomicCountConstant by positivity)
  unfold atomicKineticConstant
  nlinarith

theorem exists_atomic_small_kinetic : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ (y : Space), y≠0 → atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      (∑ p,outerKinetic (T.ensemble.vector p))≤atomicKineticConstant*(atomicCellScale y)^(-7:ℝ) := by
  obtain ⟨s,hs,hs1,hbound⟩ := exists_atomic_refined_small_scale
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha1 : a≤1 := hys.le.trans hs1
  obtain ⟨hsmall,_⟩ := hbound a ha hys
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hK⟩ := exists_atomic_physical_kinetic S hatom ψ hψ hm hE hstate hδ
    hy (Real.rpow_pos_of_pos ha (6/5:ℝ)) hsmall
    (source_patch_scale_condition ha ha1 (screenCountParameter_ge_one ψ δ))
  refine ⟨t,ht,T,ho,hcs,hos,hK.trans ?_⟩
  exact atomicKineticFormula_small hδ (le_trans zero_le_one (screenCountParameter_ge_one ψ δ))
    (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) ha ha1 hd
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem exists_atomic_near_scale_oai : ∃ s : ℝ, 0 < s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
    ∀ (u : H1Vector n), Antisymmetric u → mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
    ∀ (y : Space), y≠0 → atomicCellScale y < s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∀ {R : ℝ}, 0≤R → R≤4*atomicCellScale y →
      potentialForm (nearPotential y R) u≤atomicNearConstant*(atomicCellScale y)^(-21/5:ℝ)*R^(1/5:ℝ) := by
  obtain ⟨s,hs,hs1,Hs⟩ := exists_atomic_small_kinetic
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom u hu hm E δ hE hstate hδ y hy hys hd R hR hRa
  obtain ⟨t,ht,T,ho,hcore,hout,hK⟩ := Hs S hatom u hu hm hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have H := T.ensemble.nearPotential_le u T.law ho y hR
    (hRa.trans (by linarith [ht.1] : 4*atomicCellScale y≤t))
    (Real.rpow_pos_of_pos ha (-7:ℝ)) hcore
  rw [T.mass_eq,hm,mul_one] at H
  calc
    _≤_ := H
    _≤fermionicNearConstant*R^(1/5:ℝ)*
        ((a^(-7:ℝ))^(-2/5:ℝ)*(atomicKineticConstant*a^(-7:ℝ))+(a^(-7:ℝ))^(3/5:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg fermionicNearConstant_nonneg (Real.rpow_nonneg hR _))
      have hh := mul_le_mul_of_nonneg_left hK
        (Real.rpow_nonneg (Real.rpow_nonneg ha.le (-7)) (-2/5))
      simpa only [add_comm] using add_le_add_right hh ((a^(-7:ℝ))^(3/5:ℝ))
    _=_ := by
      rw [←Real.rpow_mul ha.le,←Real.rpow_mul ha.le]
      have he : a^((-7)*(-2/5):ℝ)*(atomicKineticConstant*a^(-7:ℝ))=
          atomicKineticConstant*a^(-21/5:ℝ) := by
        rw [mul_left_comm,←Real.rpow_add ha]
        norm_num
      rw [he]
      norm_num only at *
      unfold atomicNearConstant
      ring
end Coulomb
end

end
end

end OAI
end

theorem solution : type_of% @OAI.Coulomb.exists_atomic_near_scale_oai := @OAI.Coulomb.exists_atomic_near_scale_oai
