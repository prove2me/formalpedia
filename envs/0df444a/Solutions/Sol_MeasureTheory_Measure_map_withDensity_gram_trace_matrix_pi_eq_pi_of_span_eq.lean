-- Prove2me | solution 1 for MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9e80c545-9bc9-5a7a-bc66-dbac0fb1336c

import Mathlib
import Theorems.Thm_MeasureTheory_Measure_gram_smul_map_volume_eq_of_span_eq
import Theorems.Thm_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero
import Theorems.Thm_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace P2mGramPi

section Alg

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)]

def split (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) : (i : ι) → Matrix (Fin 2) (Fin 2) (E i) :=
  fun i => X.map (Pi.evalRingHom E i)

def unsplit (Y : (i : ι) → Matrix (Fin 2) (Fin 2) (E i)) : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) :=
  Matrix.of fun a b i => Y i a b

theorem split_unsplit (Y : (i : ι) → Matrix (Fin 2) (Fin 2) (E i)) : split E (unsplit E Y) = Y := by
  funext i; ext a b; rfl

theorem unsplit_split (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) : unsplit E (split E X) = X := by
  ext a b i; rfl

theorem split_mul (X Y : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) (i : ι) :
    split E (X * Y) i = split E X i * split E Y i :=
  Matrix.map_mul (f := Pi.evalRingHom E i)

theorem matrix_trace_apply (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) (i : ι) :
    Matrix.trace X i = Matrix.trace (split E X i) := by
  simp [Matrix.trace, split, Finset.sum_apply]

theorem det_apply (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) (i : ι) :
    Matrix.det X i = Matrix.det (split E X i) :=
  RingHom.map_det (Pi.evalRingHom E i) X

variable [∀ i, Module.Free ℝ (E i)] [∀ i, Module.Finite ℝ (E i)]

theorem leftMulMatrix_pi {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (s : ∀ i, Module.Basis (κ i) ℝ (E i)) (z : (i : ι) → E i) :
    Algebra.leftMulMatrix (Pi.basis s) z =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (s i) (z i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply, Pi.mul_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq, Pi.single_eq_same, Algebra.leftMulMatrix_eq_repr_mul]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, Pi.single_eq_of_ne' (Ne.symm h) , mul_zero, map_zero,
      Finsupp.zero_apply]

theorem trace_pi (z : (i : ι) → E i) : Algebra.trace ℝ ((i : ι) → E i) z = ∑ i, Algebra.trace ℝ (E i) (z i) := by
  classical
  let s := fun i => Module.Free.chooseBasis ℝ (E i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis s) z, leftMulMatrix_pi E s z, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ => (Algebra.trace_eq_matrix_trace (s i) (z i)).symm

theorem det_blockDiagonal' {κ : ι → Type} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (d : ∀ i, Matrix (κ i) (κ i) ℝ) : (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_

  let e : {a : Σ i, κ i // a.1 = k} ≃ κ k :=
    { toFun := fun a => cast (congrArg κ a.2) a.1.2
      invFun := fun x => ⟨⟨k, x⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨i, x⟩, hi⟩
        cases hi
        rfl
      right_inv := fun x => rfl }
  have : Matrix.toSquareBlock (Matrix.blockDiagonal' d) Sigma.fst k = (d k).reindex e.symm e.symm := by
    ext ⟨⟨i, x⟩, hi⟩ ⟨⟨j, y⟩, hj⟩
    cases hi; cases hj
    rw [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.blockDiagonal'_apply_eq,
      Matrix.reindex_apply]
    rfl
  rw [this, Matrix.det_reindex_self]

theorem norm_pi (z : (i : ι) → E i) : Algebra.norm ℝ z = ∏ i, Algebra.norm ℝ (z i) := by
  classical
  let s := fun i => Module.Free.chooseBasis ℝ (E i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis s) z, leftMulMatrix_pi E s z, det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => (Algebra.norm_eq_matrix_det (s i) (z i)).symm

theorem traceForm_split (X Y : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) :
    Algebra.trace ℝ ((i : ι) → E i) (Matrix.trace (X * Y)) =
      ∑ i, Algebra.trace ℝ (E i) (Matrix.trace (split E X i * split E Y i)) := by
  rw [trace_pi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [matrix_trace_apply, split_mul]

theorem density_split (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) :
    (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹ =
      ∏ i, (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det (split E X i))|)⁻¹ := by
  rw [norm_pi, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg _),
    ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr ENNReal.ofReal_ne_top)]
  exact Finset.prod_congr rfl fun i _ => by rw [det_apply]

end Alg

section Forms

variable (A : Type) [CommRing A] [Algebra ℝ A]

def trForm : LinearMap.BilinForm ℝ (Matrix (Fin 2) (Fin 2) A) :=
  LinearMap.mk₂ ℝ (fun X Y => Algebra.trace ℝ A (Matrix.trace (X * Y)))
    (fun X X' Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by simp only [Matrix.smul_mul, Matrix.trace_smul, map_smul])
    (fun X Y Y' => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by simp only [Matrix.mul_smul, Matrix.trace_smul, map_smul])

theorem trForm_apply (X Y : Matrix (Fin 2) (Fin 2) A) :
    trForm A X Y = Algebra.trace ℝ A (Matrix.trace (X * Y)) := rfl

def rho (X : Matrix (Fin 2) (Fin 2) A) : ℝ≥0∞ := (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹

end Forms

section Gram

variable {V : Type} [AddCommGroup V] [Module ℝ V] [MeasurableSpace V]

def gram (B : LinearMap.BilinForm ℝ V) {k : ℕ} (v : Fin k → V) : Measure V :=
  (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin k => B (v a) (v b)).det|)) •
    Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume

end Gram

section PiLemmas

theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {α : Fin n → Type}
    {mα : ∀ i, MeasurableSpace (α i)} (μ : (i : Fin n) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : Fin n) → α i → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (i : Fin n) → α i, ∏ i, g i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, g i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : α 0 × ((i : Fin n) → α (Fin.succ i)),
            g 0 x.1 * ∏ i : Fin n, g (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, g 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : α (Fin.succ i)), g (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => μ i.succ) (fun i => g i.succ) (fun i => hg i.succ), ← lintegral_prod_mul (hg 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ => (hg i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, g i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem lintegral_fintype_prod_eq_prod (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : ι) → α i → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : (i : ι) → α i, ∏ i, g i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, g i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i => μ (e i)) (fun i => g (e i)) (fun i => hg (e i))

theorem pi_smul (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (r : ι → ℝ≥0) :
    Measure.pi (fun i => (r i : ℝ≥0∞) • μ i) = (∏ i, (r i : ℝ≥0∞)) • Measure.pi μ := by
  haveI : ∀ i, SigmaFinite ((r i : ℝ≥0∞) • μ i) := fun i => (inferInstance : SigmaFinite (r i • μ i))
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem pi_withDensity (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (ρ : ∀ i, α i → ℝ≥0∞)
    (hρ : ∀ i, Measurable (ρ i)) [∀ i, SigmaFinite ((μ i).withDensity (ρ i))] :
    Measure.pi (fun i => (μ i).withDensity (ρ i)) = (Measure.pi μ).withDensity (fun x => ∏ i, ρ i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change ∫⁻ x in Set.pi univ (fun i => s i), ∏ i, ρ i (x i) ∂Measure.pi μ = _
  rw [show (∫⁻ x in Set.pi univ (fun i => s i), ∏ i, ρ i (x i) ∂Measure.pi μ) =
      ∫⁻ x, ∏ i, ρ i (x i) ∂(Measure.pi μ).restrict (Set.pi univ fun i => s i) from rfl,
    Measure.restrict_pi_pi, lintegral_fintype_prod_eq_prod _ _ hρ]
  exact Finset.prod_congr rfl fun i _ => (withDensity_apply _ (hs i)).symm

end PiLemmas

section Curry

theorem volume_map_piCurry {ι : Type} [Fintype ι] (n : ι → ℕ) :
    Measure.map (MeasurableEquiv.piCurry fun (i : ι) (_ : Fin (n i)) => ℝ) volume =
      Measure.pi fun i => (volume : Measure (Fin (n i) → ℝ)) := by
  classical
  symm
  refine Measure.pi_eq_generateFrom (C := fun i => pi univ '' pi univ fun _ : Fin (n i) => {s : Set ℝ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi) (fun i => ?_) ?_
  · exact Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℝ).toFiniteSpanningSetsIn
  · intro s hs
    choose t ht hts using hs
    have hpre : (MeasurableEquiv.piCurry fun (i : ι) (_ : Fin (n i)) => ℝ) ⁻¹' pi univ s =
        pi univ (fun σ : (Σ i, Fin (n i)) => t σ.1 σ.2) := by
      ext x
      simp only [mem_preimage, mem_univ_pi, MeasurableEquiv.coe_piCurry]
      constructor
      · intro h σ
        have := h σ.1
        rw [← hts σ.1, mem_univ_pi] at this
        exact this σ.2
      · intro h i
        rw [← hts i, mem_univ_pi]
        exact fun a => h ⟨i, a⟩
    have hmeas : ∀ i, MeasurableSet (s i) := fun i => by
      rw [← hts i]; exact MeasurableSet.univ_pi fun a => by simpa [mem_univ_pi] using ht i a
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hmeas), hpre, volume_pi_pi,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hts i, volume_pi_pi]

end Curry

section Concat

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)]

def splitL : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) ≃ₗ[ℝ] ((i : ι) → Matrix (Fin 2) (Fin 2) (E i)) where
  toFun := split E
  invFun := unsplit E
  map_add' X Y := by funext i; ext a b; rfl
  map_smul' r X := by
    funext i; ext a b
    simp only [split, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply, Pi.evalRingHom_apply]
  left_inv := unsplit_split E
  right_inv := split_unsplit E

theorem splitL_apply (X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i)) : splitL E X = split E X := rfl
theorem splitL_symm_apply (Y : (i : ι) → Matrix (Fin 2) (Fin 2) (E i)) : (splitL E).symm Y = unsplit E Y := rfl

def emb (i : ι) (X : Matrix (Fin 2) (Fin 2) (E i)) : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) :=
  unsplit E (Pi.single i X)

theorem split_emb (i : ι) (X : Matrix (Fin 2) (Fin 2) (E i)) : split E (emb E i X) = Pi.single i X := by
  rw [emb, split_unsplit]

theorem split_emb_same (i : ι) (X : Matrix (Fin 2) (Fin 2) (E i)) : split E (emb E i X) i = X := by
  rw [split_emb, Pi.single_eq_same]

theorem split_emb_ne {i j : ι} (h : j ≠ i) (X : Matrix (Fin 2) (Fin 2) (E i)) : split E (emb E i X) j = 0 := by
  rw [split_emb, Pi.single_eq_of_ne h]

variable [∀ i, Module.Free ℝ (E i)] [∀ i, Module.Finite ℝ (E i)]

theorem trForm_emb_emb (i j : ι) (X : Matrix (Fin 2) (Fin 2) (E i)) (Y : Matrix (Fin 2) (Fin 2) (E j)) :
    trForm ((i : ι) → E i) (emb E i X) (emb E j Y) =
      if h : i = j then trForm (E j) (cast (congrArg (fun k => Matrix (Fin 2) (Fin 2) (E k)) h) X) Y else 0 := by
  rw [trForm_apply, traceForm_split]
  by_cases h : i = j
  · subst h
    rw [dif_pos rfl, cast_eq, Finset.sum_eq_single i]
    · rw [split_emb_same, split_emb_same, trForm_apply]
    · intro k _ hk
      rw [split_emb_ne E hk, zero_mul, Matrix.trace_zero, map_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · have hkj : k ≠ j := fun hkj => h (hk.symm.trans hkj)
      rw [split_emb_ne E hkj Y, mul_zero, Matrix.trace_zero, map_zero]
    · rw [split_emb_ne E hk X, zero_mul, Matrix.trace_zero, map_zero]

end Concat

section Meas

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)]
  [∀ i, Module.Free ℝ (E i)] [∀ i, Module.Finite ℝ (E i)] [∀ i, TopologicalSpace (E i)]
  [∀ i, IsTopologicalRing (E i)] [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
  [∀ i, MeasurableSpace (Matrix (Fin 2) (Fin 2) (E i))] [∀ i, BorelSpace (Matrix (Fin 2) (Fin 2) (E i))]
  [MeasurableSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))] [BorelSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))]

theorem continuous_algebraNorm (i : ι) : Continuous (Algebra.norm ℝ : E i → ℝ) := by
  classical
  let b := Module.finBasis ℝ (E i)
  have h : (Algebra.norm ℝ : E i → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : E i => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

theorem measurable_rho (i : ι) : Measurable (rho (E i)) := by
  have hc : Continuous fun X : Matrix (Fin 2) (Fin 2) (E i) => |Algebra.norm ℝ (Matrix.det X)| :=
    continuous_abs.comp ((continuous_algebraNorm E i).comp (continuous_id.matrix_det))
  exact (ENNReal.continuous_ofReal.comp hc).measurable.inv

theorem rho_ne_top_iff {A : Type} [CommRing A] [Algebra ℝ A] (X : Matrix (Fin 2) (Fin 2) A) :
    rho A X ≠ ∞ ↔ Algebra.norm ℝ (Matrix.det X) ≠ 0 := by
  rw [rho, ne_eq, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero, not_le, abs_pos]

theorem sigmaFinite_map_coord (i : ι) {k : ℕ} (v : Fin k → Matrix (Fin 2) (Fin 2) (E i)) (hli : LinearIndependent ℝ v) :
    SigmaFinite (Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume) := by
  have hLapply : ∀ c : Fin k → ℝ, Fintype.linearCombination ℝ v c = ∑ a, c a • v a := fun c => by
    simp [Fintype.linearCombination_apply]
  have hinj : Function.Injective (Fintype.linearCombination ℝ v) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hce : Topology.IsClosedEmbedding (Fintype.linearCombination ℝ v) :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hemb : MeasurableEmbedding (fun c : Fin k → ℝ => ∑ a, c a • v a) := by
    have : (fun c : Fin k → ℝ => ∑ a, c a • v a) = Fintype.linearCombination ℝ v := funext fun c => (hLapply c).symm
    rw [this]; exact hce.measurableEmbedding
  exact hemb.sigmaFinite_map

theorem sigmaFinite_gram (i : ι) {k : ℕ} (v : Fin k → Matrix (Fin 2) (Fin 2) (E i)) (hli : LinearIndependent ℝ v) :
    SigmaFinite (gram (trForm (E i)) v) := by
  haveI := sigmaFinite_map_coord E i v hli
  unfold gram
  exact (inferInstance : SigmaFinite ((Real.toNNReal _) • Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume))

theorem sigmaFinite_gram_withDensity (i : ι) (W : Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    {k : ℕ} (v : Fin k → Matrix (Fin 2) (Fin 2) (E i))
    (hv : LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = W)
    (hW : ∃ X ∈ W, Algebra.norm ℝ (Matrix.det X) ≠ 0) :
    SigmaFinite ((gram (trForm (E i)) v).withDensity (rho (E i))) := by
  classical
  obtain ⟨hli, hsp⟩ := hv
  have hLapply : ∀ c : Fin k → ℝ, Fintype.linearCombination ℝ v c = ∑ a, c a • v a := fun c => by
    simp [Fintype.linearCombination_apply]
  have hinj : Function.Injective (Fintype.linearCombination ℝ v) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hli
  have hce : Topology.IsClosedEmbedding (Fintype.linearCombination ℝ v) :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hemb : MeasurableEmbedding (fun c : Fin k → ℝ => ∑ a, c a • v a) := by
    have : (fun c : Fin k → ℝ => ∑ a, c a • v a) = Fintype.linearCombination ℝ v := funext fun c => (hLapply c).symm
    rw [this]; exact hce.measurableEmbedding
  haveI : SigmaFinite (Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume) := hemb.sigmaFinite_map
  haveI : SigmaFinite (gram (trForm (E i)) v) := by
    unfold gram
    exact (inferInstance : SigmaFinite ((Real.toNNReal _) • Measure.map (fun c : Fin k → ℝ => ∑ a, c a • v a) volume))
  refine SigmaFinite.withDensity_of_ne_top ?_
  unfold gram
  refine Measure.ae_smul_measure ?_ _
  rw [ae_map_iff (p := fun X => rho (E i) X ≠ ∞) hemb.measurable.aemeasurable
    ((measurable_rho E i) (MeasurableSet.compl (measurableSet_singleton _)))]

  obtain ⟨P, hP⟩ := Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul (E i) (Fin 2) k v
  have hP0 : P ≠ 0 := by
    obtain ⟨X, hX, hN⟩ := hW
    rw [← hsp] at hX
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
    intro h
    apply hN
    rw [← hP c, h, map_zero]
  have hnull := MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero P hP0
  rw [ae_iff]
  refine measure_mono_null (fun c hc => ?_) hnull
  simp only [Set.mem_setOf_eq, rho_ne_top_iff, not_not] at hc
  show MvPolynomial.eval c P = 0
  rw [hP c]; exact hc

theorem map_withDensity_comp {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (μ : Measure α) {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = (Measure.map f μ).withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hρ hf]
  rfl

theorem measurable_split : Measurable (split E) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact (continuous_id.matrix_map (continuous_apply i)).measurable

def rhoPi (Y : (i : ι) → Matrix (Fin 2) (Fin 2) (E i)) : ℝ≥0∞ := ∏ i, rho (E i) (Y i)

theorem measurable_rhoPi : Measurable (rhoPi E) :=
  Finset.measurable_prod _ fun i _ => (measurable_rho E i).comp (measurable_pi_apply i)

theorem rho_eq_rhoPi_split : rho ((i : ι) → E i) = rhoPi E ∘ split E := by
  funext X; exact density_split E X

theorem main
    (W : ∀ i, Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    (n : ι → ℕ) (e : ∀ i, Fin (n i) → Matrix (Fin 2) (Fin 2) (E i))
    (he : ∀ i, LinearIndependent ℝ (e i) ∧ Submodule.span ℝ (Set.range (e i)) = W i)
    (hW : ∀ i, ∃ X ∈ W i, Algebra.norm ℝ (Matrix.det X) ≠ 0)
    (W' : Submodule ℝ (Matrix (Fin 2) (Fin 2) ((i : ι) → E i)))
    (hW' : ∀ X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i), X ∈ W' ↔ ∀ i, X.map (Pi.evalRingHom E i) ∈ W i)
    (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ((i : ι) → E i))
    (hf : LinearIndependent ℝ f ∧ Submodule.span ℝ (Set.range f) = W') :
    Measure.map (split E) ((gram (trForm ((i : ι) → E i)) f).withDensity (rho ((i : ι) → E i))) =
      Measure.pi (fun i => (gram (trForm (E i)) (e i)).withDensity (rho (E i))) := by
  classical
  haveI hσf : ∀ i, SigmaFinite ((gram (trForm (E i)) (e i)).withDensity (rho (E i))) := fun i =>
    sigmaFinite_gram_withDensity E i (W i) (e i) (he i) (hW i)

  set K := (Σ i, Fin (n i)) with hK
  let g : (Σ i, Fin (n i)) → Matrix (Fin 2) (Fin 2) ((i : ι) → E i) := fun κ => emb E κ.1 (e κ.1 κ.2)
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  let f' : Fin (Fintype.card (Σ i, Fin (n i))) → Matrix (Fin 2) (Fin 2) ((i : ι) → E i) := g ∘ σ
  have hsplit_g : ∀ κ : (Σ i, Fin (n i)), split E (g κ) = Pi.single κ.1 (e κ.1 κ.2) := fun κ => split_emb E _ _
  have hg_li : LinearIndependent ℝ g := by
    have h := (Pi.linearIndependent_single (fun i => e i) (fun i => (he i).1)).map' (splitL E).symm.toLinearMap
      (LinearEquiv.ker _)
    exact h
  have hf'_li : LinearIndependent ℝ f' := (linearIndependent_equiv σ).mpr hg_li
  have hg_span : Submodule.span ℝ (Set.range g) = W' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨κ, rfl⟩
      rw [SetLike.mem_coe, hW']
      intro i
      change split E (g κ) i ∈ W i
      rw [hsplit_g]
      by_cases h : i = κ.1
      · subst h; rw [Pi.single_eq_same, ← (he _).2]; exact Submodule.subset_span ⟨κ.2, rfl⟩
      · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _
    · intro X hX
      rw [hW'] at hX
      have hXi : ∀ i, ∃ c : Fin (n i) → ℝ, split E X i = ∑ a, c a • e i a := fun i => by
        have := hX i
        rw [← (he i).2] at this
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp this
        exact ⟨c, hc.symm⟩
      choose c hc using hXi
      have hXeq : X = ∑ κ : (Σ i, Fin (n i)), c κ.1 κ.2 • g κ := by
        apply (splitL E).injective
        rw [map_sum]
        funext i
        simp only [map_smul, splitL_apply, Finset.sum_apply, Pi.smul_apply, hsplit_g]
        rw [hc i, Fintype.sum_sigma]
        rw [Finset.sum_eq_single i]
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [Pi.single_eq_same]
        · intro j _ hj
          refine Finset.sum_eq_zero fun a _ => ?_
          rw [Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
        · exact fun h => absurd (Finset.mem_univ i) h
      rw [hXeq]
      exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ, rfl⟩)
  have hf'_span : Submodule.span ℝ (Set.range f') = W' := by
    rw [show Set.range f' = Set.range g from σ.surjective.range_comp g, hg_span]

  have hB := MeasureTheory.Measure.gram_smul_map_volume_eq_of_span_eq (trForm ((i : ι) → E i)) f f' hf.1 hf'_li
    (by rw [hf'_span, hf.2])
  have hgram : gram (trForm ((i : ι) → E i)) f = gram (trForm ((i : ι) → E i)) f' := by
    unfold gram; exact hB.symm
  rw [hgram]

  have hlin : Measurable fun c : Fin (Fintype.card (Σ i, Fin (n i))) → ℝ => ∑ a, c a • f' a :=
    (continuous_finset_sum _ fun a _ => (continuous_apply a).smul continuous_const).measurable
  rw [rho_eq_rhoPi_split, gram, map_withDensity_comp (measurable_split E) _ (measurable_rhoPi E),
    Measure.map_smul, Measure.map_map (measurable_split E) hlin]

  have hσfin : ∀ i, SigmaFinite (Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume) :=
    fun i => sigmaFinite_map_coord E i (e i) (he i).1
  have hcoordg : Measurable fun d : (Σ i, Fin (n i)) → ℝ => ∑ κ, d κ • g κ :=
    (continuous_finset_sum _ fun κ _ => (continuous_apply κ).smul continuous_const).measurable
  have hstep1 : Measure.map (split E ∘ fun c : Fin (Fintype.card (Σ i, Fin (n i))) → ℝ => ∑ a, c a • f' a) volume =
      Measure.map (split E ∘ fun d : (Σ i, Fin (n i)) → ℝ => ∑ κ, d κ • g κ) volume := by
    have hre := (volume_measurePreserving_piCongrLeft (fun _ : (Σ i, Fin (n i)) => ℝ) σ).map_eq
    rw [← hre, Measure.map_map ((measurable_split E).comp hcoordg) (MeasurableEquiv.measurable _)]
    congr 1
    funext c
    simp only [Function.comp_apply]
    congr 1
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  have hstep2 : (split E ∘ fun d : (Σ i, Fin (n i)) → ℝ => ∑ κ, d κ • g κ) =
      (fun (y : (i : ι) → (Fin (n i) → ℝ)) (i : ι) => ∑ a, y i a • e i a) ∘
        (MeasurableEquiv.piCurry fun (i : ι) (_ : Fin (n i)) => ℝ) := by
    funext d
    funext i
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCurry, Sigma.curry]
    rw [← splitL_apply, map_sum]
    simp only [map_smul, splitL_apply, Finset.sum_apply, Pi.smul_apply, hsplit_g]
    rw [Fintype.sum_sigma, Finset.sum_eq_single i]
    · exact Finset.sum_congr rfl fun a _ => by rw [Pi.single_eq_same]
    · intro j _ hj
      exact Finset.sum_eq_zero fun a _ => by rw [Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  have hΦ : ∀ i, Measurable fun c : Fin (n i) → ℝ => ∑ a, c a • e i a := fun i =>
    (continuous_finset_sum _ fun a _ => (continuous_apply a).smul continuous_const).measurable
  have hΦm : Measurable (fun (y : (i : ι) → (Fin (n i) → ℝ)) (i : ι) => ∑ a, y i a • e i a) :=
    measurable_pi_lambda _ fun i => (hΦ i).comp (measurable_pi_apply i)
  have hstep3 : Measure.map (split E ∘ fun c : Fin (Fintype.card (Σ i, Fin (n i))) → ℝ => ∑ a, c a • f' a) volume =
      Measure.pi fun i => Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume := by
    rw [hstep1, hstep2, ← Measure.map_map hΦm (MeasurableEquiv.measurable _), volume_map_piCurry]
    exact Measure.pi_map_pi fun i => (hΦ i).aemeasurable
  rw [hstep3]

  have hdet : (Matrix.of fun a b : Fin (Fintype.card (Σ i, Fin (n i))) => trForm ((i : ι) → E i) (f' a) (f' b)).det =
      ∏ i, (Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)).det := by
    have h1 : (Matrix.of fun a b : Fin (Fintype.card (Σ i, Fin (n i))) => trForm ((i : ι) → E i) (f' a) (f' b)) =
        Matrix.reindex σ.symm σ.symm
          (Matrix.blockDiagonal' fun i => Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)) := by
      ext a b
      simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.of_apply, Matrix.submatrix_apply]
      change trForm ((i : ι) → E i) (g (σ a)) (g (σ b)) = Matrix.blockDiagonal' _ (σ a) (σ b)
      generalize σ a = κa
      generalize σ b = κb
      rcases κa with ⟨i, x⟩
      rcases κb with ⟨j, y⟩
      change trForm ((i : ι) → E i) (emb E i (e i x)) (emb E j (e j y)) = _
      rw [trForm_emb_emb, Matrix.blockDiagonal'_apply']
      by_cases h : i = j
      · subst h; simp
      · rw [dif_neg h, dif_neg h]
    rw [h1, Matrix.det_reindex_self, det_blockDiagonal']
  have hsqrt : ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (Fintype.card (Σ i, Fin (n i))) =>
        trForm ((i : ι) → E i) (f' a) (f' b)).det|) =
      ∏ i, ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)).det|) := by
    rw [hdet, Finset.abs_prod, Real.sqrt_prod _ fun i _ => abs_nonneg _,
      ENNReal.ofReal_prod_of_nonneg fun i _ => Real.sqrt_nonneg _]
  rw [hsqrt]

  have hsmul := pi_smul (fun i => Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume)
    (fun i => (Real.sqrt |(Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)).det|).toNNReal)
  have hcoe : ∀ i, (((Real.sqrt |(Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)).det|).toNNReal : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) => trForm (E i) (e i a) (e i b)).det|) := fun i => rfl
  simp only [hcoe] at hsmul
  rw [← hsmul]
  haveI : ∀ i, SigmaFinite (gram (trForm (E i)) (e i)) := fun i => sigmaFinite_gram E i (e i) (he i).1
  have hwd := pi_withDensity (fun i => gram (trForm (E i)) (e i)) (fun i => rho (E i)) (fun i => measurable_rho E i)
  unfold gram at hwd
  rw [show rhoPi E = fun Y => ∏ i, rho (E i) (Y i) from rfl]
  exact hwd.symm

end Meas

end P2mGramPi

end

open P2mGramPi in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → Type) [∀ i, CommRing (E i)] [∀ i, Algebra ℝ (E i)] [∀ i, Module.Free ℝ (E i)]
    [∀ i, Module.Finite ℝ (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, IsTopologicalRing (E i)]
    [∀ i, ContinuousSMul ℝ (E i)] [∀ i, T2Space (E i)]
    [∀ i, MeasurableSpace (Matrix (Fin 2) (Fin 2) (E i))] [∀ i, BorelSpace (Matrix (Fin 2) (Fin 2) (E i))]
    [MeasurableSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))] [BorelSpace (Matrix (Fin 2) (Fin 2) ((i : ι) → E i))]
    (W : ∀ i, Submodule ℝ (Matrix (Fin 2) (Fin 2) (E i)))
    (n : ι → ℕ) (e : ∀ i, Fin (n i) → Matrix (Fin 2) (Fin 2) (E i))
    (he : ∀ i, LinearIndependent ℝ (e i) ∧ Submodule.span ℝ (Set.range (e i)) = W i)
    (hW : ∀ i, ∃ X ∈ W i, Algebra.norm ℝ (Matrix.det X) ≠ 0)
    (W' : Submodule ℝ (Matrix (Fin 2) (Fin 2) ((i : ι) → E i)))
    (hW' : ∀ X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i), X ∈ W' ↔ ∀ i, X.map (Pi.evalRingHom E i) ∈ W i)
    (N : ℕ) (f : Fin N → Matrix (Fin 2) (Fin 2) ((i : ι) → E i))
    (hf : LinearIndependent ℝ f ∧ Submodule.span ℝ (Set.range f) = W') :
    Measure.map (fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => fun i : ι => X.map (Pi.evalRingHom E i))
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin N =>
              Algebra.trace ℝ ((i : ι) → E i) (Matrix.trace (f a * f b))).det|)) •
            Measure.map (fun c : Fin N → ℝ => ∑ a, c a • f a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) ((i : ι) → E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) =
      Measure.pi (fun i : ι =>
        ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun a b : Fin (n i) =>
              Algebra.trace ℝ (E i) (Matrix.trace (e i a * e i b))).det|)) •
            Measure.map (fun c : Fin (n i) → ℝ => ∑ a, c a • e i a) volume).withDensity
          fun X : Matrix (Fin 2) (Fin 2) (E i) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) :=
  main E W n e he hW W' hW' N f hf

end S_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq
end P2MW
export P2MW.S_MeasureTheory_Measure_map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq (solution)
