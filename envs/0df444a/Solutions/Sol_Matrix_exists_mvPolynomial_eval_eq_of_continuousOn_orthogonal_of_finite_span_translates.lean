-- Prove2me | solution 1 for Matrix.exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/256b9caf-3599-52cb-902c-a67a3c201dfe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates

set_option autoImplicit false

open MeasureTheory

namespace KFinPolyAux

variable (n : ℕ)

abbrev K : Type := ↥(Matrix.orthogonalGroup (Fin n) ℝ)

theorem entry_abs_le_one (o : K n) (i j : Fin n) : |(o : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
  have h := o.2
  rw [Matrix.mem_orthogonalGroup_iff'] at h

  have hcol : ∑ a, (o : Matrix (Fin n) (Fin n) ℝ) a j * (o : Matrix (Fin n) (Fin n) ℝ) a j = 1 := by
    have := congrFun (congrFun h j) j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this
  have hle : (o : Matrix (Fin n) (Fin n) ℝ) i j * (o : Matrix (Fin n) (Fin n) ℝ) i j ≤ 1 := by
    rw [← hcol]
    exact Finset.single_le_sum (f := fun a => (o : Matrix (Fin n) (Fin n) ℝ) a j * (o : Matrix (Fin n) (Fin n) ℝ) a j)
      (fun a _ => mul_self_nonneg _) (Finset.mem_univ i)
  exact abs_le_one_iff_mul_self_le_one.2 hle

theorem isCompact_carrier : IsCompact (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  have hbox : IsCompact {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have : {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1} =
        Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
      ext A
      exact Iff.intro (fun h i _ j _ => h i j) (fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _))
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hclosed : IsClosed (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) := by
    have : (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) =
        (fun A : Matrix (Fin n) (Fin n) ℝ => A.transpose * A) ⁻¹' {1} := by
      ext A; simp [Matrix.mem_orthogonalGroup_iff']
    rw [this]
    exact (isClosed_singleton.preimage ((continuous_id.matrix_transpose).matrix_mul continuous_id))
  refine hbox.of_isClosed_subset hclosed ?_
  intro A hA i j
  have := entry_abs_le_one n ⟨A, hA⟩ i j
  exact abs_le.1 this

scoped instance : CompactSpace (K n) := isCompact_iff_compactSpace.1 (isCompact_carrier n)

scoped instance : MeasurableSpace (K n) := borel (K n)
scoped instance : BorelSpace (K n) := ⟨rfl⟩

noncomputable example : Measure (K n) := Measure.haar
example : LocallyCompactSpace (K n) := inferInstance
example : IsTopologicalGroup (K n) := inferInstance

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

variable {n : ℕ}

noncomputable def μK : Measure (K n) := Measure.haar

scoped instance : IsFiniteMeasure (μK : Measure (K n)) := by unfold μK; infer_instance
scoped instance : (μK : Measure (K n)).IsMulLeftInvariant := by unfold μK; infer_instance
scoped instance : (μK : Measure (K n)).IsOpenPosMeasure := by unfold μK; infer_instance
scoped instance : IsFiniteMeasureOnCompacts (μK : Measure (K n)) := by unfold μK; infer_instance

noncomputable def rt (f : C(K n, ℂ)) (r : K n) : C(K n, ℂ) := f.comp ⟨fun o => o * r, continuous_mul_const r⟩

@[scoped simp] theorem rt_apply (f : C(K n, ℂ)) (r o : K n) : rt f r o = f (o * r) := rfl

theorem continuous_rt (f : C(K n, ℂ)) : Continuous (rt f) := by
  have h : Continuous (fun p : K n × K n => f (p.2 * p.1)) := f.continuous.comp (continuous_snd.mul continuous_fst)
  let F : C(K n × K n, ℂ) := ⟨fun p => f (p.2 * p.1), h⟩
  have : rt f = F.curry := by
    ext r o; rfl
  rw [this]
  exact F.curry.continuous

noncomputable def W (f : C(K n, ℂ)) : Submodule ℂ C(K n, ℂ) := Submodule.span ℂ (Set.range (rt f))

theorem rt_mem_W (f : C(K n, ℂ)) (r : K n) : rt f r ∈ W f := Submodule.subset_span ⟨r, rfl⟩

theorem finite_W (f : C(K n, ℂ)) (m : ℕ) (g : Fin m → K n → ℂ)
    (hg : ∀ r : K n, ∃ a : Fin m → ℂ, ∀ o : K n, f (o * r) = ∑ l, a l * g l o) :
    Module.Finite ℂ (W f) := by

  let ι : C(K n, ℂ) →ₗ[ℂ] (K n → ℂ) :=
    { toFun := fun h => (h : K n → ℂ), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun h₁ h₂ h => ContinuousMap.ext (congrFun h)
  let S : Submodule ℂ (K n → ℂ) := Submodule.span ℂ (Set.range g)
  haveI : Module.Finite ℂ S := Module.Finite.span_of_finite ℂ (Set.finite_range g)
  have hmap : ∀ w ∈ W f, ι w ∈ S := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ι w ∈ S) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨r, rfl⟩
      obtain ⟨a, ha⟩ := hg r
      have : ι (rt f r) = ∑ l, a l • g l := by
        funext o
        show f (o * r) = (∑ l, a l • g l) o
        rw [ha o, Finset.sum_apply]
        rfl
      rw [this]
      exact S.sum_mem fun l _ => S.smul_mem _ (Submodule.subset_span ⟨l, rfl⟩)
    · exact S.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact S.add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact S.smul_mem c hx
  let ι' : W f →ₗ[ℂ] S := (ι.domRestrict (W f)).codRestrict S (fun w => hmap w w.2)
  have hι' : Function.Injective ι' := by
    intro x y h
    apply Subtype.ext
    apply hι
    have := congrArg Subtype.val h
    exact this
  exact Module.Finite.of_injective ι' hι'

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

variable {n : ℕ}

theorem integrable_of_continuous (g : K n → ℂ) (hg : Continuous g) : Integrable g μK := by
  have := hg.continuousOn.integrableOn_compact (μ := μK) isCompact_univ
  simpa [integrableOn_univ] using this

noncomputable def conv (f φ : C(K n, ℂ)) (o₀ : K n) : ℂ := ∫ o, f (o₀ * o) * φ o ∂μK

theorem exists_mem_W_conv (f φ : C(K n, ℂ)) [Module.Finite ℂ (W f)] :
    ∃ w ∈ W f, ∀ o₀, conv f φ o₀ = w o₀ := by
  let b := Module.finBasis ℂ (W f)
  let T' : K n → W f := fun r => ⟨rt f r, rt_mem_W f r⟩
  have hT' : Continuous T' := (continuous_rt f).subtype_mk _
  let a : Fin (Module.finrank ℂ (W f)) → K n → ℂ := fun l r => b.coord l (T' r)
  have ha : ∀ l, Continuous (a l) := fun l =>
    (LinearMap.continuous_of_finiteDimensional (b.coord l)).comp hT'
  have hexp : ∀ r o₀, f (o₀ * r) = ∑ l, a l r * (b l : C(K n, ℂ)) o₀ := fun r o₀ => by
    have h1 : (T' r : C(K n, ℂ)) = ∑ l, b.repr (T' r) l • (b l : C(K n, ℂ)) := by
      have := congrArg Subtype.val (b.sum_repr (T' r)).symm
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this
    have := congrArg (fun g : C(K n, ℂ) => g o₀) h1
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact this
  refine ⟨∑ l, (∫ o, a l o * φ o ∂μK) • (b l : C(K n, ℂ)),
    Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (b l).2), fun o₀ => ?_⟩
  simp only [conv, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hint : ∀ l, Integrable (fun o => a l o * φ o * (b l : C(K n, ℂ)) o₀) μK := fun l =>
    integrable_of_continuous _ (((ha l).mul φ.continuous).mul continuous_const)
  calc ∫ o, f (o₀ * o) * φ o ∂μK = ∫ o, ∑ l, a l o * φ o * (b l : C(K n, ℂ)) o₀ ∂μK := by
        congr 1; funext o; rw [hexp, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ l, ∫ o, a l o * φ o * (b l : C(K n, ℂ)) o₀ ∂μK := integral_finsetSum _ fun l _ => hint l
    _ = ∑ l, (∫ o, a l o * φ o ∂μK) * (b l : C(K n, ℂ)) o₀ :=
        Finset.sum_congr rfl fun l _ => integral_mul_const _ _

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

variable {n : ℕ}

scoped instance : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  show SecondCountableTopology (Fin n → Fin n → ℝ) from inferInstance

example : MeasurableMul (K n) := inferInstance

def cE (o : K n) (ij : Fin n × Fin n) : ℂ := (((o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)

theorem continuous_cE (ij : Fin n × Fin n) : Continuous fun o : K n => cE o ij := by
  unfold cE
  have h : Continuous fun o : K n => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 :=
    (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)
  exact Complex.continuous_ofReal.comp h

noncomputable def pev (P : MvPolynomial (Fin n × Fin n) ℂ) (o : K n) : ℂ := MvPolynomial.eval (cE o) P

theorem continuous_pev (P : MvPolynomial (Fin n × Fin n) ℂ) : Continuous (pev (n := n) P) :=
  (MvPolynomial.continuous_eval P).comp (continuous_pi fun ij => continuous_cE ij)

noncomputable def pevC (P : MvPolynomial (Fin n × Fin n) ℂ) : C(K n, ℂ) := ⟨pev P, continuous_pev P⟩

@[scoped simp] theorem pevC_apply (P : MvPolynomial (Fin n × Fin n) ℂ) (o : K n) : pevC P o = pev P o := rfl

theorem cE_inv_mul (o₀ x : K n) (i j : Fin n) :
    cE (o₀⁻¹ * x) (i, j) = ∑ a, cE o₀ (a, i) * cE x (a, j) := by
  unfold cE
  simp only
  rw [show ((o₀⁻¹ * x : K n) : Matrix (Fin n) (Fin n) ℝ) = (o₀⁻¹ : K n) * (x : Matrix (Fin n) (Fin n) ℝ) from rfl,
    Matrix.UnitaryGroup.inv_apply, Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.star_apply, star_trivial]

theorem sep (P : MvPolynomial (Fin n × Fin n) ℂ) :
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → K n → ℂ) (v : ι → MvPolynomial (Fin n × Fin n) ℂ),
      (∀ i, Continuous (u i)) ∧ ∀ x o₀ : K n, pev P (o₀⁻¹ * x) = ∑ i, u i x * pev (v i) o₀ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Unit, inferInstance, fun _ _ => a, fun _ => 1, fun _ => continuous_const, fun x o₀ => ?_⟩
    simp [pev]
  | add p q hp hq =>
    obtain ⟨ι₁, _, u₁, v₁, hu₁, h₁⟩ := hp
    obtain ⟨ι₂, _, u₂, v₂, hu₂, h₂⟩ := hq
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim u₁ u₂, Sum.elim v₁ v₂, ?_, fun x o₀ => ?_⟩
    · rintro (i | i)
      · exact hu₁ i
      · exact hu₂ i
    · rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, pev, map_add] at *
      rw [h₁, h₂]
  | mul_X p ij hp =>
    obtain ⟨ι, _, u, v, hu, h⟩ := hp
    refine ⟨ι × Fin n, inferInstance, fun ka x => u ka.1 x * cE x (ka.2, ij.2),
      fun ka => v ka.1 * MvPolynomial.X (ka.2, ij.1), fun ka => (hu ka.1).mul (continuous_cE _), fun x o₀ => ?_⟩
    have hX : pev (p * MvPolynomial.X ij) (o₀⁻¹ * x) = pev p (o₀⁻¹ * x) * cE (o₀⁻¹ * x) ij := by
      simp [pev, MvPolynomial.eval_X]
    rw [hX, h, show ij = (ij.1, ij.2) from rfl, cE_inv_mul, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [pev, map_mul, MvPolynomial.eval_X]
    ring

theorem exists_pev_conv (f : C(K n, ℂ)) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℂ, ∀ o₀, conv f (pevC P) o₀ = pev Q o₀ := by
  obtain ⟨ι, _, u, v, hu, h⟩ := sep P
  refine ⟨∑ i, MvPolynomial.C (∫ o, f o * u i o ∂μK) * v i, fun o₀ => ?_⟩
  have hint : ∀ i, Integrable (fun o => f o * u i o * pev (v i) o₀) μK := fun i =>
    integrable_of_continuous _ ((f.continuous.mul (hu i)).mul continuous_const)
  calc conv f (pevC P) o₀ = ∫ o, (fun y => f y * pev P (o₀⁻¹ * y)) (o₀ * o) ∂μK := by
        simp only [conv, pevC_apply, inv_mul_cancel_left]
    _ = ∫ o, f o * pev P (o₀⁻¹ * o) ∂μK := integral_mul_left_eq_self (μ := μK) (fun y => f y * pev P (o₀⁻¹ * y)) o₀
    _ = ∫ o, ∑ i, f o * u i o * pev (v i) o₀ ∂μK := by
        congr 1; funext o; rw [h, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∫ o, f o * u i o * pev (v i) o₀ ∂μK := integral_finsetSum _ fun i _ => hint i
    _ = ∑ i, (∫ o, f o * u i o ∂μK) * pev (v i) o₀ := Finset.sum_congr rfl fun i _ => integral_mul_const _ _
    _ = pev (∑ i, MvPolynomial.C (∫ o, f o * u i o ∂μK) * v i) o₀ := by
        simp only [pev, map_sum, map_mul, MvPolynomial.eval_C]

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

variable {n : ℕ}

theorem integrableR_of_continuous (g : K n → ℝ) (hg : Continuous g) : Integrable g μK := by
  have := hg.continuousOn.integrableOn_compact (μ := μK) isCompact_univ
  simpa [integrableOn_univ] using this

noncomputable def ofRealC (g : C(K n, ℝ)) : C(K n, ℂ) := ⟨fun o => (g o : ℂ), Complex.continuous_ofReal.comp g.continuous⟩

@[scoped simp] theorem ofRealC_apply (g : C(K n, ℝ)) (o : K n) : ofRealC g o = (g o : ℂ) := rfl

theorem exists_conv_sub_le (f : C(K n, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(K n, ℝ), ∀ o₀, ‖conv f (ofRealC g) o₀ - f o₀‖ ≤ ε := by

  let D : K n → C(K n, ℂ) := fun o => rt f o - f
  have hD : Continuous D := (continuous_rt f).sub continuous_const
  let Uset : Set (K n) := {o | ‖D o‖ < ε}
  have hU : IsOpen Uset := isOpen_lt (continuous_norm.comp hD) continuous_const
  have h1U : (1 : K n) ∈ Uset := by
    show ‖D 1‖ < ε
    have : D 1 = 0 := by ext o; simp [D, rt_apply]
    rw [this, norm_zero]; exact hε
  have hclose : ∀ o ∈ Uset, ∀ o₀, ‖f (o₀ * o) - f o₀‖ ≤ ε := fun o ho o₀ => by
    have := (D o).norm_coe_le_norm o₀
    simp only [D, ContinuousMap.coe_sub, Pi.sub_apply, rt_apply] at this
    exact this.trans (le_of_lt ho)

  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl isClosed_singleton
    (Set.disjoint_singleton_right.2 (fun h => h h1U))
  have hgnn : ∀ o, 0 ≤ g o := fun o => (hg01 o).1
  have hI : 0 < ∫ o, g o ∂μK :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      hgnn (by rw [hg1 (Set.mem_singleton 1)]; exact one_ne_zero)
  set I : ℝ := ∫ o, g o ∂μK with hIdef
  let φr : C(K n, ℝ) := (I⁻¹ : ℝ) • g
  have hφr : ∀ o, φr o = I⁻¹ * g o := fun o => rfl
  have hφnn : ∀ o, 0 ≤ φr o := fun o => by rw [hφr]; exact mul_nonneg (inv_nonneg.2 hI.le) (hgnn o)
  have hφint : ∫ o, φr o ∂μK = 1 := by
    simp only [hφr, integral_const_mul]
    exact inv_mul_cancel₀ hI.ne'
  have hφsupp : ∀ o, o ∉ Uset → φr o = 0 := fun o ho => by
    rw [hφr, show g o = 0 from hg0 ho, mul_zero]
  refine ⟨φr, fun o₀ => ?_⟩

  have hgi : Integrable (fun o => (φr o : ℂ)) μK :=
    integrable_of_continuous _ (Complex.continuous_ofReal.comp φr.continuous)
  have hint1 : Integrable (fun o => f (o₀ * o) * (φr o : ℂ)) μK :=
    integrable_of_continuous _ ((f.continuous.comp (continuous_const_mul o₀)).mul (Complex.continuous_ofReal.comp φr.continuous))
  have hint2 : Integrable (fun o => f o₀ * (φr o : ℂ)) μK := hgi.const_mul _
  have hrepr : conv f (ofRealC φr) o₀ - f o₀ = ∫ o, (f (o₀ * o) - f o₀) * (φr o : ℂ) ∂μK := by
    have hone : ∫ o, f o₀ * (φr o : ℂ) ∂μK = f o₀ := by
      rw [integral_const_mul, integral_complex_ofReal, hφint]; simp
    simp only [conv, ofRealC_apply]
    rw [show (fun o => (f (o₀ * o) - f o₀) * (φr o : ℂ)) = fun o => f (o₀ * o) * (φr o : ℂ) - f o₀ * (φr o : ℂ) from
      funext fun o => by ring, integral_sub hint1 hint2, hone]
  rw [hrepr]
  have hbound : ∀ o, ‖(f (o₀ * o) - f o₀) * (φr o : ℂ)‖ ≤ ε * φr o := fun o => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφnn o)]
    by_cases ho : o ∈ Uset
    · exact mul_le_mul_of_nonneg_right (hclose o ho o₀) (hφnn o)
    · rw [hφsupp o ho, mul_zero, mul_zero]
  calc ‖∫ o, (f (o₀ * o) - f o₀) * (φr o : ℂ) ∂μK‖ ≤ ∫ o, ε * φr o ∂μK :=
        norm_integral_le_of_norm_le (integrableR_of_continuous _ (continuous_const.mul φr.continuous))
          (Filter.Eventually.of_forall hbound)
    _ = ε := by rw [integral_const_mul, hφint, mul_one]

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

variable {n : ℕ}

def coordR (ij : Fin n × Fin n) : C(K n, ℝ) :=
  ⟨fun o => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2,
    (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)⟩

noncomputable def polyR : Subalgebra ℝ C(K n, ℝ) := (MvPolynomial.aeval (R := ℝ) (coordR (n := n))).range

theorem aeval_coordR_apply (P : MvPolynomial (Fin n × Fin n) ℝ) (o : K n) :
    (MvPolynomial.aeval (R := ℝ) (coordR (n := n)) P) o =
      MvPolynomial.eval (fun ij => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, MvPolynomial.aeval_X, ContinuousMap.mul_apply, hp, MvPolynomial.eval_X]
    rfl

theorem polyR_separatesPoints : (polyR (n := n)).SeparatesPoints := by
  intro x y hxy
  have : ∃ ij : Fin n × Fin n, (x : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 ≠ (y : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (Matrix.ext fun i j => by simpa using h (i, j)))
  obtain ⟨ij, hij⟩ := this
  refine ⟨coordR ij, ⟨coordR ij, ⟨MvPolynomial.X ij, MvPolynomial.aeval_X _ _⟩, rfl⟩, hij⟩

theorem exists_poly_close (g : C(K n, ℝ)) (η : ℝ) (hη : 0 < η) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℝ, ∀ o,
      |g o - MvPolynomial.eval (fun ij => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2) P| ≤ η := by
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyR_separatesPoints (n := n))
  have hmem : g ∈ (polyR (n := n)).topologicalClosure := by rw [htop]; exact Algebra.mem_top
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨a, ⟨P, rfl⟩, hdist⟩ := hmem η hη
  refine ⟨P, fun o => ?_⟩
  rw [← aeval_coordR_apply]
  have h1 := ContinuousMap.norm_coe_le_norm (g - MvPolynomial.aeval (R := ℝ) (coordR (n := n)) P) o
  rw [ContinuousMap.coe_sub, Pi.sub_apply, Real.norm_eq_abs] at h1
  rw [dist_eq_norm] at hdist
  exact h1.trans hdist.le

theorem norm_conv_sub_conv_le (f φ ψ : C(K n, ℂ)) (η : ℝ) (h : ∀ o, ‖φ o - ψ o‖ ≤ η) (o₀ : K n) :
    ‖conv f φ o₀ - conv f ψ o₀‖ ≤ ‖f‖ * η * (μK : Measure (K n)).real Set.univ := by
  have hint : ∀ χ : C(K n, ℂ), Integrable (fun o => f (o₀ * o) * χ o) μK := fun χ =>
    integrable_of_continuous _ ((f.continuous.comp (continuous_const_mul o₀)).mul χ.continuous)
  simp only [conv]
  rw [← integral_sub (hint φ) (hint ψ)]
  have hb : ∀ o, ‖f (o₀ * o) * φ o - f (o₀ * o) * ψ o‖ ≤ ‖f‖ * η := fun o => by
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm _) (h o) (norm_nonneg _) (norm_nonneg _)
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)

noncomputable def Wp (f : C(K n, ℂ)) : Submodule ℂ C(K n, ℂ) where
  carrier := {w | w ∈ W f ∧ ∃ Q : MvPolynomial (Fin n × Fin n) ℂ, ∀ o, w o = pev Q o}
  add_mem' := by
    rintro a b ⟨ha, Qa, hQa⟩ ⟨hb, Qb, hQb⟩
    exact ⟨(W f).add_mem ha hb, Qa + Qb, fun o => by simp [hQa o, hQb o, pev]⟩
  zero_mem' := ⟨(W f).zero_mem, 0, fun o => by simp [pev]⟩
  smul_mem' := by
    rintro c a ⟨ha, Qa, hQa⟩
    exact ⟨(W f).smul_mem c ha, MvPolynomial.C c * Qa, fun o => by simp [hQa o, pev]⟩

theorem Wp_le (f : C(K n, ℂ)) : Wp f ≤ W f := fun _ hw => hw.1

theorem eval₂_ofReal_cE (o : K n) (Pr : MvPolynomial (Fin n × Fin n) ℝ) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) (cE o) Pr =
      ((MvPolynomial.eval (fun ij => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2) Pr : ℝ) : ℂ) := by
  induction Pr using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.eval₂_C]
  | add p q hp hq => rw [MvPolynomial.eval₂_add, hp, hq, map_add, Complex.ofReal_add]
  | mul_X p ij hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hp, map_mul, MvPolynomial.eval_X, Complex.ofReal_mul]
    rfl

theorem main_K (f : C(K n, ℂ)) [Module.Finite ℂ (W f)] :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℂ, ∀ o, f o = pev Q o := by
  haveI : Module.Finite ℂ (Wp f) := Module.Finite.of_injective (Submodule.inclusion (Wp_le f))
    (Submodule.inclusion_injective _)
  have hclosed : IsClosed (Wp f : Set C(K n, ℂ)) := Submodule.closed_of_finiteDimensional _
  suffices hmem : f ∈ closure (Wp f : Set C(K n, ℂ)) by
    rw [hclosed.closure_eq] at hmem
    exact hmem.2
  rw [Metric.mem_closure_iff]
  intro ε hε

  obtain ⟨g, hg⟩ := exists_conv_sub_le f (ε / 3) (by positivity)

  set M : ℝ := ‖f‖ * (μK : Measure (K n)).real Set.univ + 1 with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  obtain ⟨Pr, hPr⟩ := exists_poly_close g (ε / 3 / M) (by positivity)
  let P : MvPolynomial (Fin n × Fin n) ℂ := MvPolynomial.map (algebraMap ℝ ℂ) Pr
  have hPeval : ∀ o, pev P o = ((MvPolynomial.eval (fun ij => (o : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2) Pr : ℝ) : ℂ) :=
    fun o => by
      show MvPolynomial.eval (cE o) (MvPolynomial.map (algebraMap ℝ ℂ) Pr) = _
      rw [MvPolynomial.eval_map, eval₂_ofReal_cE]

  have hclosePφ : ∀ o, ‖ofRealC g o - pevC P o‖ ≤ ε / 3 / M := fun o => by
    rw [ofRealC_apply, pevC_apply, hPeval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hPr o

  obtain ⟨w, hwW, hw⟩ := exists_mem_W_conv f (pevC P)
  obtain ⟨Q, hQ⟩ := exists_pev_conv f P
  have hwp : w ∈ Wp f := ⟨hwW, Q, fun o => by rw [← hw o, hQ o]⟩
  refine ⟨w, hwp, ?_⟩
  rw [dist_eq_norm]
  have hK1 : 0 ≤ (μK : Measure (K n)).real Set.univ := by positivity
  have hpt : ∀ o₀, ‖(f - w) o₀‖ ≤ 2 * ε / 3 := fun o₀ => by
    rw [ContinuousMap.coe_sub, Pi.sub_apply, ← hw o₀]
    have h1 := hg o₀
    have h2 := norm_conv_sub_conv_le f (ofRealC g) (pevC P) (ε / 3 / M) hclosePφ o₀
    have h3 : ‖f‖ * (ε / 3 / M) * (μK : Measure (K n)).real Set.univ ≤ ε / 3 := by
      rw [show ‖f‖ * (ε / 3 / M) * (μK : Measure (K n)).real Set.univ =
        (ε / 3) * ((‖f‖ * (μK : Measure (K n)).real Set.univ) / M) by ring]
      have : (‖f‖ * (μK : Measure (K n)).real Set.univ) / M ≤ 1 := by
        rw [div_le_one hM0, hM]; linarith
      calc (ε / 3) * ((‖f‖ * (μK : Measure (K n)).real Set.univ) / M) ≤ (ε / 3) * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = ε / 3 := mul_one _
    calc ‖f o₀ - conv f (pevC P) o₀‖
        = ‖(f o₀ - conv f (ofRealC g) o₀) + (conv f (ofRealC g) o₀ - conv f (pevC P) o₀)‖ := by ring_nf
      _ ≤ ‖f o₀ - conv f (ofRealC g) o₀‖ + ‖conv f (ofRealC g) o₀ - conv f (pevC P) o₀‖ := norm_add_le _ _
      _ ≤ ε / 3 + ε / 3 := add_le_add (by rw [norm_sub_rev]; exact h1) (h2.trans h3)
      _ = 2 * ε / 3 := by ring
  have hne : Nonempty (K n) := ⟨1⟩
  calc ‖f - w‖ ≤ 2 * ε / 3 := (ContinuousMap.norm_le _ (by positivity)).2 hpt
    _ < ε := by linarith

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

namespace KFinPolyAux

p2m_open_scoped "ContinuousMap MeasureTheory.ContinuousMap"

theorem mem_orthogonalGroup_of_iff {n : ℕ} (o : Fin n → Fin n → ℝ) :
    Matrix.of o ∈ Matrix.orthogonalGroup (Fin n) ℝ ↔ ∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0 := by
  rw [Matrix.mem_orthogonalGroup_iff']
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp [Matrix.of_apply]

end KFinPolyAux
p2m_reactivate "P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.KFinPolyAux"

open KFinPolyAux in
theorem solution
    (n : ℕ) (f : (Fin n → Fin n → ℝ) → ℂ)
    (hf : ContinuousOn f {o : Fin n → Fin n → ℝ | ∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0})
    (hfin : ∃ (m : ℕ) (g : Fin m → (Fin n → Fin n → ℝ) → ℂ),
      ∀ r : Fin n → Fin n → ℝ, (∀ i j : Fin n, ∑ a : Fin n, r a i * r a j = if i = j then 1 else 0) →
        ∃ a : Fin m → ℂ, ∀ o : Fin n → Fin n → ℝ,
          (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
          f (fun i j => ∑ k : Fin n, o i k * r k j) = ∑ l, a l * g l o) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ o : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
      f o = MvPolynomial.eval (fun ij : Fin n × Fin n => ((o ij.1 ij.2 : ℝ) : ℂ)) P := by

  have hmem : ∀ o : K n, ((o : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ) ∈
      {o : Fin n → Fin n → ℝ | ∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0} :=
    fun o => (mem_orthogonalGroup_of_iff _).1 o.2
  let fK : C(K n, ℂ) := ⟨fun o => f (o : Matrix (Fin n) (Fin n) ℝ), hf.comp_continuous continuous_subtype_val hmem⟩
  obtain ⟨m, g, hg⟩ := hfin
  haveI : Module.Finite ℂ (W fK) := by
    refine finite_W fK m (fun l o => g l (o : Matrix (Fin n) (Fin n) ℝ)) fun r => ?_
    obtain ⟨a, ha⟩ := hg (r : Matrix (Fin n) (Fin n) ℝ) (hmem r)
    refine ⟨a, fun o => ?_⟩
    have := ha (o : Matrix (Fin n) (Fin n) ℝ) (hmem o)
    show f ((o * r : K n) : Matrix (Fin n) (Fin n) ℝ) = _
    rw [← this]
    congr 1
  obtain ⟨Q, hQ⟩ := main_K fK
  refine ⟨Q, fun o ho => ?_⟩
  have := hQ ⟨Matrix.of o, (mem_orthogonalGroup_of_iff o).2 ho⟩
  exact this

end S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates
end P2MW
export P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates (solution)
