-- Prove2me | solution 1 for GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:55.621142+00:00
-- url     : https://prove2.me/submissions/6179b3f7-c926-4564-8a86-2398f25f5218

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
namespace GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]
private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)
private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul, IA (Units.mk0 _ hA) rfl, hinv, map_mul, mul_smul]
private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl
end GlobalTheory.SplitWeil
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f
end GlobalTheory.SplitWeil
