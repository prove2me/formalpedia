-- Prove2me | solution 1 for MomentDRO.Conf.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:36:25.035847+00:00
-- url     : https://prove2.me/submissions/d94fcd29-09bc-4fdc-b558-869f3ae4fa7d

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

open MeasureTheory ProbabilityTheory MomentDRO.Conf Matrix
open scoped BigOperators NNReal

namespace Lemma2Aux

universe u

/-- Bounded differences with constant c in every coordinate. -/
def BD {X : Type u} {n : ℕ} (f : (Fin n → X) → ℝ) (c : ℝ) : Prop :=
  ∀ (S S' : Fin n → X) (i : Fin n), (∀ j, j ≠ i → S j = S' j) → |f S - f S'| ≤ c

lemma bint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ ω, |F ω| ≤ B) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

lemma int_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Ω → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ ω, |F ω| ≤ B) (t C : ℝ) :
    Integrable (fun ω => Real.exp (t * (F ω - C))) μ := by
  refine Integrable.of_bound
    (Real.measurable_exp.comp ((hF.sub_const C).const_mul t)).aestronglyMeasurable
    (Real.exp (|t| * (B + |C|))) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
  have h1 := abs_le.1 (hb ω)
  have h2 : |F ω - C| ≤ B + |C| :=
    abs_le.2 ⟨by linarith [le_abs_self C], by linarith [neg_abs_le C]⟩
  calc t * (F ω - C) ≤ |t * (F ω - C)| := le_abs_self _
    _ = |t| * |F ω - C| := abs_mul _ _
    _ ≤ |t| * (B + |C|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

section McDiarmid

variable {X : Type u} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]

/-- Integrating out the first coordinate. -/
noncomputable def marg {n : ℕ} (f : (Fin (n + 1) → X) → ℝ) (S' : Fin n → X) : ℝ :=
  ∫ x, f (Fin.cons x S') ∂P

lemma meas_cons {n : ℕ} {Φ : (Fin (n + 1) → X) → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun z : X × (Fin n → X) => Φ (Fin.cons z.1 z.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  have heq : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have h : (fun z : X × (Fin n → X) => Φ (Fin.cons z.1 z.2)) = fun z => Φ (e.symm z) :=
    funext fun z => by rw [heq]
  rw [h]
  exact hΦ.comp e.symm.measurable

lemma integral_cons {n : ℕ} {Φ : (Fin (n + 1) → X) → ℝ}
    (hint : Integrable (fun z : X × (Fin n → X) => Φ (Fin.cons z.1 z.2)) (P.prod (Measure.pi (fun _ : Fin (n) => P)))) :
    ∫ S, Φ S ∂(Measure.pi (fun _ : Fin (n + 1) => P)) = ∫ S', ∫ x, Φ (Fin.cons x S') ∂P ∂(Measure.pi (fun _ : Fin (n) => P)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
  have mp : MeasurePreserving e (Measure.pi (fun _ : Fin (n + 1) => P)) (P.prod (Measure.pi (fun _ : Fin (n) => P))) :=
    measurePreserving_piFinSuccAbove (fun _ => P) 0
  have heq : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  calc ∫ S, Φ S ∂(Measure.pi (fun _ : Fin (n + 1) => P)) = ∫ z, Φ (e.symm z) ∂(P.prod (Measure.pi (fun _ : Fin (n) => P))) :=
        ((mp.symm e).integral_comp' Φ).symm
    _ = ∫ z, Φ (Fin.cons z.1 z.2) ∂(P.prod (Measure.pi (fun _ : Fin (n) => P))) := by simp only [heq]
    _ = ∫ S', ∫ x, Φ (Fin.cons x S') ∂P ∂(Measure.pi (fun _ : Fin (n) => P)) := integral_prod_symm _ hint

lemma marg_measurable {n : ℕ} {f : (Fin (n + 1) → X) → ℝ} (hf : Measurable f) :
    Measurable (marg P f) :=
  ((meas_cons hf).stronglyMeasurable.integral_prod_left' (μ := P)).measurable

lemma meas_cons_left {n : ℕ} {f : (Fin (n + 1) → X) → ℝ} (hf : Measurable f) (S' : Fin n → X) :
    Measurable (fun x : X => f (Fin.cons x S')) :=
  (meas_cons hf).comp (measurable_id.prodMk measurable_const)

lemma marg_bound {n : ℕ} {f : (Fin (n + 1) → X) → ℝ} {B : ℝ} (hB : ∀ S, |f S| ≤ B)
    (S' : Fin n → X) : |marg P f S'| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun x => f (Fin.cons x S')) (C := B)
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB _)
  simpa [marg] using h

lemma marg_BD {n : ℕ} {f : (Fin (n + 1) → X) → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ S, |f S| ≤ B) {c : ℝ} (hbd : BD f c) : BD (marg P f) c := by
  intro S1 S2 i hS
  have hd : marg P f S1 - marg P f S2 =
      ∫ x, (f (Fin.cons x S1) - f (Fin.cons x S2)) ∂P := by
    unfold marg
    rw [integral_sub (bint P (meas_cons_left hf S1) fun x => hB _)
      (bint P (meas_cons_left hf S2) fun x => hB _)]
  rw [hd]
  have h := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun x => f (Fin.cons x S1) - f (Fin.cons x S2)) (C := c)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      refine hbd _ _ i.succ fun j => ?_
      induction j using Fin.cases with
      | zero => intro _; simp
      | succ k =>
        intro hk
        simp only [Fin.cons_succ]
        exact hS k fun h => hk (by rw [h]))
  simpa using h

/-- McDiarmid's bound on the moment generating function. -/
theorem mgf_bound [Nonempty X] (c B : ℝ) (hc : 0 ≤ c) :
    ∀ (n : ℕ) (f : (Fin n → X) → ℝ), Measurable f → (∀ S, |f S| ≤ B) → BD f c → ∀ t : ℝ,
      ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi (fun _ : Fin (n) => P)))) ∂(Measure.pi (fun _ : Fin (n) => P)) ≤
        Real.exp (n * (c ^ 2 * t ^ 2 / 8)) := by
  intro n
  induction n with
  | zero =>
    intro f hf hB hbd t
    have hconst : ∀ S, f S = f finZeroElim := fun S => congrArg f (Subsingleton.elim _ _)
    have h1 : ∫ S', f S' ∂(Measure.pi (fun _ : Fin (0) => P)) = f finZeroElim := by
      rw [integral_congr_ae (ae_of_all _ hconst)]
      simp
    have hI : ∀ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi (fun _ : Fin (0) => P)))) = 1 := by
      intro S
      rw [h1, hconst S, sub_self, mul_zero, Real.exp_zero]
    simp only [hI]
    simp
  | succ n ih =>
    intro f hf hB hbd t
    have hEf : ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)) = ∫ S', marg P f S' ∂(Measure.pi (fun _ : Fin (n) => P)) :=
      integral_cons P (bint _ (meas_cons hf) fun z => hB _)
    have hint2 : Integrable (fun z : X × (Fin n → X) =>
        Real.exp (t * (f (Fin.cons z.1 z.2) - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P))))) (P.prod (Measure.pi (fun _ : Fin (n) => P))) :=
      int_exp _ (meas_cons hf) (fun z => hB _) t _
    have step1 : ∫ S, Real.exp (t * (f S - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂(Measure.pi (fun _ : Fin (n + 1) => P)) =
        ∫ S', ∫ x, Real.exp (t * (f (Fin.cons x S') - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂P ∂(Measure.pi (fun _ : Fin (n) => P)) :=
      integral_cons P (Φ := fun S => Real.exp (t * (f S - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P))))) hint2
    have inner : ∀ S' : Fin n → X,
        ∫ x, Real.exp (t * (f (Fin.cons x S') - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂P ≤
          Real.exp (c ^ 2 * t ^ 2 / 8) *
            Real.exp (t * (marg P f S' - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) := by
      intro S'
      have hsplit : ∀ x, Real.exp (t * (f (Fin.cons x S') - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) =
          Real.exp (t * (f (Fin.cons x S') - marg P f S')) *
            Real.exp (t * (marg P f S' - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) := by
        intro x
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [hsplit]
      rw [integral_mul_const]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hbdd : BddBelow (Set.range fun x : X => f (Fin.cons x S')) :=
        ⟨-B, by rintro _ ⟨x, rfl⟩; exact (abs_le.1 (hB _)).1⟩
      have hd0 : ∀ x x' : X, |f (Fin.cons x S') - f (Fin.cons x' S')| ≤ c := by
        intro x x'
        refine hbd _ _ 0 fun j => ?_
        induction j using Fin.cases with
        | zero => intro h0; exact absurd rfl h0
        | succ k => intro _; simp
      have hIcc : ∀ x : X, f (Fin.cons x S') ∈
          Set.Icc (⨅ x : X, f (Fin.cons x S')) ((⨅ x : X, f (Fin.cons x S')) + c) := by
        intro x
        refine ⟨ciInf_le hbdd x, ?_⟩
        have h : f (Fin.cons x S') - c ≤ ⨅ x : X, f (Fin.cons x S') :=
          le_ciInf fun x' => by linarith [(abs_le.1 (hd0 x x')).2]
        linarith
      have H := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := fun x : X => f (Fin.cons x S'))
        (meas_cons_left hf S').aemeasurable (ae_of_all _ hIcc)
      have H2 := H.mgf_le t
      have hcoe : (((‖(⨅ x : X, f (Fin.cons x S')) + c - ⨅ x : X, f (Fin.cons x S')‖₊ / 2) ^ 2 :
          ℝ≥0) : ℝ) = (c / 2) ^ 2 := by
        rw [add_sub_cancel_left]
        simp [abs_of_nonneg hc]
      rw [hcoe] at H2
      calc ∫ x, Real.exp (t * (f (Fin.cons x S') - marg P f S')) ∂P
          = mgf (fun x : X => f (Fin.cons x S') - ∫ x, f (Fin.cons x S') ∂P) P t := rfl
        _ ≤ Real.exp ((c / 2) ^ 2 * t ^ 2 / 2) := H2
        _ = Real.exp (c ^ 2 * t ^ 2 / 8) := by ring_nf
    calc ∫ S, Real.exp (t * (f S - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂(Measure.pi (fun _ : Fin (n + 1) => P))
        = ∫ S', ∫ x, Real.exp (t * (f (Fin.cons x S') - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂P ∂(Measure.pi (fun _ : Fin (n) => P)) := step1
      _ ≤ ∫ S', Real.exp (c ^ 2 * t ^ 2 / 8) *
            Real.exp (t * (marg P f S' - ∫ S, f S ∂(Measure.pi (fun _ : Fin (n + 1) => P)))) ∂(Measure.pi (fun _ : Fin (n) => P)) :=
          integral_mono hint2.integral_prod_right
            ((int_exp _ (marg_measurable P hf) (marg_bound P hB) t _).const_mul _) inner
      _ = Real.exp (c ^ 2 * t ^ 2 / 8) *
            ∫ S', Real.exp (t * (marg P f S' - ∫ S'', marg P f S'' ∂(Measure.pi (fun _ : Fin (n) => P)))) ∂(Measure.pi (fun _ : Fin (n) => P)) := by
          rw [integral_const_mul, hEf]
      _ ≤ Real.exp (c ^ 2 * t ^ 2 / 8) * Real.exp (n * (c ^ 2 * t ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left
            (ih (marg P f) (marg_measurable P hf) (marg_bound P hB) (marg_BD P hf hB hbd) t)
            (Real.exp_pos _).le
      _ = Real.exp ((n + 1 : ℕ) * (c ^ 2 * t ^ 2 / 8)) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

end McDiarmid

end Lemma2Aux

namespace Lemma2Aux

variable {m M : ℕ}

/-- Truncation to the ball of radius R. -/
noncomputable def clip (R : ℝ) (x : Fin m → ℝ) : Fin m → ℝ := if x ⬝ᵥ x ≤ R ^ 2 then x else 0

noncomputable def yv (R : ℝ) (x : Fin m → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (clip R x)

noncomputable def Wv (R : ℝ) (S : Fin M → (Fin m → ℝ)) : EuclideanSpace ℝ (Fin m) :=
  (M : ℝ)⁻¹ • ∑ i, yv R (S i)

/-- Norm of the mean of the truncated sample. -/
noncomputable def fn (R : ℝ) (S : Fin M → (Fin m → ℝ)) : ℝ := ‖Wv R S‖

lemma norm_sq_toLp (v : Fin m → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

lemma yv_measurable (R : ℝ) : Measurable (yv (m := m) R) := by
  have hdm : Measurable (fun x : Fin m → ℝ => x ⬝ᵥ x) := by
    simp only [dotProduct]
    fun_prop
  have hclip : Measurable (clip (m := m) R) := by
    show Measurable (fun x : Fin m → ℝ => if x ⬝ᵥ x ≤ R ^ 2 then x else 0)
    exact Measurable.ite (measurableSet_le hdm measurable_const) measurable_id measurable_const
  exact (WithLp.measurable_toLp 2 _).comp hclip

lemma yv_norm_le {R : ℝ} (hR : 0 ≤ R) (x : Fin m → ℝ) : ‖yv R x‖ ≤ R := by
  have h1 : ‖yv R x‖ ^ 2 ≤ R ^ 2 := by
    rw [yv, norm_sq_toLp, clip]
    split_ifs with h
    · exact h
    · rw [dotProduct_zero]
      positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 h1

lemma fn_measurable (R : ℝ) : Measurable (fn (m := m) (M := M) R) := by
  have hW : Measurable (Wv (m := m) (M := M) R) := by
    unfold Wv
    exact Measurable.const_smul (Finset.measurable_sum _ fun i _ =>
      (yv_measurable R).comp (measurable_pi_apply i)) ((M : ℝ)⁻¹)
  exact hW.norm

lemma fn_bound {R : ℝ} (hR : 0 ≤ R) (hM : 0 < M) (S : Fin M → (Fin m → ℝ)) : |fn R S| ≤ R := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rw [fn, abs_of_nonneg (norm_nonneg _), Wv, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hMpos)]
  calc (M : ℝ)⁻¹ * ‖∑ i, yv R (S i)‖ ≤ (M : ℝ)⁻¹ * ∑ _i : Fin M, R := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => yv_norm_le hR _)
    _ = R := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma fn_BD {R : ℝ} (hR : 0 ≤ R) (hM : 0 < M) : BD (fn (m := m) (M := M) R) (2 * R / M) := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  intro S S' i hS
  have hdiff : Wv R S - Wv R S' = (M : ℝ)⁻¹ • (yv R (S i) - yv R (S' i)) := by
    rw [Wv, Wv, ← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [hS j hj, sub_self]
  calc |fn R S - fn R S'| ≤ ‖Wv R S - Wv R S'‖ := abs_norm_sub_norm_le _ _
    _ = (M : ℝ)⁻¹ * ‖yv R (S i) - yv R (S' i)‖ := by
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hMpos)]
    _ ≤ (M : ℝ)⁻¹ * (R + R) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (yv_norm_le hR _) (yv_norm_le hR _))
    _ = 2 * R / M := by ring

lemma fn_sq {R : ℝ} (S : Fin M → (Fin m → ℝ)) (hS : ∀ i, S i ⬝ᵥ S i ≤ R ^ 2) :
    fn R S ^ 2 = empMean S ⬝ᵥ empMean S := by
  have h1 : Wv R S = WithLp.toLp 2 (empMean S) := by
    simp only [Wv, yv, clip, empMean, WithLp.toLp_smul, WithLp.toLp_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (hS i)]
  rw [fn, h1, norm_sq_toLp]

lemma second_moment (Pζ : Measure (Fin m → ℝ)) [IsProbabilityMeasure Pζ]
    (hL2 : ∀ i : Fin m, MemLp (fun ξ : Fin m → ℝ => ξ i) 2 Pζ) (hmean : meanVec Pζ = 0)
    (a : Fin m) :
    Integrable (fun S : Fin M → (Fin m → ℝ) => (∑ i, S i a) ^ 2) (Measure.pi (fun _ : Fin M => Pζ)) ∧
      ∫ S : Fin M → (Fin m → ℝ), (∑ i, S i a) ^ 2 ∂(Measure.pi (fun _ : Fin M => Pζ)) = M * ∫ ξ, ξ a ^ 2 ∂Pζ := by
  have hindep : iIndepFun (fun (i : Fin M) (S : Fin M → (Fin m → ℝ)) => S i a) (Measure.pi (fun _ : Fin M => Pζ)) :=
    iIndepFun_pi (X := fun (_ : Fin M) (ξ : Fin m → ℝ) => ξ a)
      (fun i => (measurable_pi_apply a).aemeasurable)
  have hmem : ∀ i : Fin M, MemLp (fun S : Fin M → (Fin m → ℝ) => S i a) 2 (Measure.pi (fun _ : Fin M => Pζ)) := fun i =>
    (hL2 a).comp_measurePreserving (measurePreserving_eval (fun _ : Fin M => Pζ) i)
  have hmean0 : ∀ i : Fin M, ∫ S : Fin M → (Fin m → ℝ), S i a ∂(Measure.pi (fun _ : Fin M => Pζ)) = 0 := fun i =>
    (integral_comp_eval (μ := fun _ : Fin M => Pζ) (i := i) (f := fun ξ : Fin m → ℝ => ξ a)
      (measurable_pi_apply a).aestronglyMeasurable).trans (congrFun hmean a)
  have hvar : ∀ i : Fin M,
      Var[fun S : Fin M → (Fin m → ℝ) => S i a; (Measure.pi (fun _ : Fin M => Pζ))] = ∫ ξ, ξ a ^ 2 ∂Pζ := fun i =>
    (variance_of_integral_eq_zero
      ((measurable_pi_apply a).comp (measurable_pi_apply i)).aemeasurable (hmean0 i)).trans
      (integral_comp_eval (μ := fun _ : Fin M => Pζ) (i := i)
        (f := fun ξ : Fin m → ℝ => ξ a ^ 2)
        ((measurable_pi_apply a).pow_const 2).aestronglyMeasurable)
  have hsumvar : Var[fun S : Fin M → (Fin m → ℝ) => ∑ i, S i a; (Measure.pi (fun _ : Fin M => Pζ))] =
      ∑ i : Fin M, Var[fun S : Fin M → (Fin m → ℝ) => S i a; (Measure.pi (fun _ : Fin M => Pζ))] := by
    have h := IndepFun.variance_sum (μ := (Measure.pi (fun _ : Fin M => Pζ)))
      (X := fun (i : Fin M) (S : Fin M → (Fin m → ℝ)) => S i a) (s := Finset.univ)
      (fun i _ => hmem i) (fun i _ j _ hij => hindep.indepFun hij)
    have hfun : (∑ i : Fin M, fun S : Fin M → (Fin m → ℝ) => S i a) = fun S => ∑ i, S i a := by
      funext S
      simp [Finset.sum_apply]
    rw [← hfun]
    exact h
  have hsm : Measurable (fun S : Fin M → (Fin m → ℝ) => ∑ i, S i a) :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply a).comp (measurable_pi_apply i)
  have hsum0 : ∫ S : Fin M → (Fin m → ℝ), ∑ i, S i a ∂(Measure.pi (fun _ : Fin M => Pζ)) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable one_le_two)]
    simp [hmean0]
  have hv2 := variance_of_integral_eq_zero (μ := (Measure.pi (fun _ : Fin M => Pζ))) hsm.aemeasurable hsum0
  refine ⟨(memLp_finsetSum _ fun i _ => hmem i).integrable_sq, hv2.symm.trans (hsumvar.trans ?_)⟩
  rw [Finset.sum_congr rfl fun i _ => hvar i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma second_moment_fn (Pζ : Measure (Fin m → ℝ)) [IsProbabilityMeasure Pζ]
    (hL2 : ∀ i : Fin m, MemLp (fun ξ : Fin m → ℝ => ξ i) 2 Pζ) (hmean : meanVec Pζ = 0)
    {R : ℝ} (hM : 0 < M) (hbound : ∀ᵐ ζ ∂Pζ, ζ ⬝ᵥ ζ ≤ R ^ 2) :
    ∫ S, fn (m := m) (M := M) R S ^ 2 ∂(Measure.pi (fun _ : Fin M => Pζ)) ≤ R ^ 2 / M := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hA : ∀ᵐ S ∂(Measure.pi (fun _ : Fin M => Pζ)), ∀ i, S i ⬝ᵥ S i ≤ R ^ 2 := ae_all_iff.2 fun i => by
    have h := (Measure.quasiMeasurePreserving_eval (fun _ : Fin M => Pζ) i).ae hbound
    exact h
  have hae : (fun S : Fin M → (Fin m → ℝ) => fn R S ^ 2) =ᵐ[(Measure.pi (fun _ : Fin M => Pζ))]
      fun S => ∑ a, ((M : ℝ)⁻¹ * ∑ i, S i a) ^ 2 := by
    filter_upwards [hA] with S hS
    rw [fn_sq S hS]
    simp only [empMean, dotProduct, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, pow_two]
  rw [integral_congr_ae hae]
  have hsm := fun a => second_moment (M := M) Pζ hL2 hmean a
  have hR2 : ∫ _ξ : Fin m → ℝ, R ^ 2 ∂Pζ = R ^ 2 := by simp
  calc ∫ S : Fin M → (Fin m → ℝ), ∑ a, ((M : ℝ)⁻¹ * ∑ i, S i a) ^ 2 ∂(Measure.pi (fun _ : Fin M => Pζ))
      = ∑ a, ∫ S : Fin M → (Fin m → ℝ), ((M : ℝ)⁻¹ * ∑ i, S i a) ^ 2 ∂(Measure.pi (fun _ : Fin M => Pζ)) :=
        integral_finsetSum _ fun a _ => by
          simp only [mul_pow]
          exact (hsm a).1.const_mul _
    _ = ∑ a, ((M : ℝ)⁻¹) ^ 2 * (M * ∫ ξ, ξ a ^ 2 ∂Pζ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [mul_pow]
        rw [integral_const_mul, (hsm a).2]
    _ = (M : ℝ)⁻¹ * ∑ a, ∫ ξ, ξ a ^ 2 ∂Pζ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        field_simp
    _ = (M : ℝ)⁻¹ * ∫ ξ, ∑ a, ξ a ^ 2 ∂Pζ := by
        rw [integral_finsetSum _ fun a _ => (hL2 a).integrable_sq]
    _ ≤ (M : ℝ)⁻¹ * R ^ 2 := by
        have h : ∫ ξ, ∑ a, ξ a ^ 2 ∂Pζ ≤ ∫ _ξ : Fin m → ℝ, R ^ 2 ∂Pζ :=
          integral_mono_ae (integrable_finsetSum _ fun a _ => (hL2 a).integrable_sq)
            (integrable_const _)
            (by filter_upwards [hbound] with ξ hξ; simpa [dotProduct, pow_two] using hξ)
        rw [hR2] at h
        exact mul_le_mul_of_nonneg_left h (inv_pos.2 hMpos).le
    _ = R ^ 2 / M := by ring

end Lemma2Aux

theorem solution {m M : ℕ} (Pζ : Measure (Fin m → ℝ)) (R : ℝ)
    (hζ : IsNormalized Pζ R) (hM : 0 < M) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤ sampleLaw Pζ M
      {S | empMean S ⬝ᵥ empMean S ≤ betaC M R δ} := by
  obtain ⟨⟨hprob, hL2⟩, hmean, -, hR, hbound⟩ := hζ
  have := hprob
  change ENNReal.ofReal (1 - δ) ≤ (Measure.pi (fun _ : Fin M => Pζ)) {S | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hA : ∀ᵐ S ∂(Measure.pi (fun _ : Fin M => Pζ)), ∀ i, S i ⬝ᵥ S i ≤ R ^ 2 := ae_all_iff.2 fun i => by
    have h := (Measure.quasiMeasurePreserving_eval (fun _ : Fin M => Pζ) i).ae hbound
    exact h
  have hβ : 0 ≤ betaC M R δ := by
    unfold betaC
    positivity
  have key : ∃ bad : Set (Fin M → (Fin m → ℝ)), (Measure.pi (fun _ : Fin M => Pζ)) bad ≤ ENNReal.ofReal δ ∧
      ∀ S : Fin M → (Fin m → ℝ), (∀ i, S i ⬝ᵥ S i ≤ R ^ 2) → S ∉ bad →
        empMean S ⬝ᵥ empMean S ≤ betaC M R δ := by
    rcases hR.eq_or_lt with hR0 | hRpos
    · refine ⟨∅, by simp, fun S hS _ => ?_⟩
      have hz : ∀ i, S i = 0 := fun i => by
        have h1 : S i ⬝ᵥ S i ≤ 0 := by
          have h := hS i
          rw [← hR0] at h
          simpa using h
        have h2 : 0 ≤ S i ⬝ᵥ S i := Finset.sum_nonneg fun a _ => mul_self_nonneg _
        exact dotProduct_self_eq_zero.1 (le_antisymm h1 h2)
      have hem : empMean S = 0 := by simp [empMean, hz]
      rw [hem, dotProduct_zero]
      exact hβ
    · obtain ⟨Ef, hEf⟩ : ∃ Ef : ℝ, Ef = ∫ S, Lemma2Aux.fn (m := m) (M := M) R S ∂(Measure.pi (fun _ : Fin M => Pζ)) :=
        ⟨_, rfl⟩
      have hfm := Lemma2Aux.fn_measurable (m := m) (M := M) R
      have hfB := Lemma2Aux.fn_bound (m := m) (M := M) hR hM
      have hbd := Lemma2Aux.fn_BD (m := m) (M := M) hR hM
      have hE2 := Lemma2Aux.second_moment_fn (M := M) Pζ hL2 hmean hM hbound
      have hfL2 : MemLp (Lemma2Aux.fn (m := m) (M := M) R) 2 (Measure.pi (fun _ : Fin M => Pζ)) :=
        MemLp.of_bound hfm.aestronglyMeasurable R
          (ae_of_all _ fun S => by rw [Real.norm_eq_abs]; exact hfB S)
      have hv := variance_nonneg (Lemma2Aux.fn (m := m) (M := M) R) (Measure.pi (fun _ : Fin M => Pζ))
      rw [variance_eq_sub hfL2, ← hEf] at hv
      have hsq : ∫ S, (Lemma2Aux.fn (m := m) (M := M) R ^ 2) S ∂(Measure.pi (fun _ : Fin M => Pζ)) =
          ∫ S, Lemma2Aux.fn (m := m) (M := M) R S ^ 2 ∂(Measure.pi (fun _ : Fin M => Pζ)) := rfl
      have hEf2 : Ef ^ 2 ≤ R ^ 2 / M := by linarith
      have hEfle : Ef ≤ R / Real.sqrt M := by
        have h1 : |Ef| ≤ Real.sqrt (R ^ 2 / M) := Real.abs_le_sqrt hEf2
        rw [Real.sqrt_div (sq_nonneg R), Real.sqrt_sq hR] at h1
        exact (le_abs_self _).trans h1
      have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
      obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = R / Real.sqrt M * Real.sqrt (2 * Real.log (1 / δ)) :=
        ⟨_, rfl⟩
      have hε0 : 0 ≤ ε := by rw [hε]; positivity
      have hε2 : ε ^ 2 = R ^ 2 / M * (2 * Real.log (1 / δ)) := by
        rw [hε, mul_pow, div_pow, Real.sq_sqrt hMpos.le, Real.sq_sqrt (by positivity)]
      obtain ⟨cc, hcc⟩ : ∃ cc : ℝ≥0, (cc : ℝ) = R ^ 2 / M :=
        ⟨⟨R ^ 2 / M, by positivity⟩, rfl⟩
      have Hsg : HasSubgaussianMGF (fun S => Lemma2Aux.fn (m := m) (M := M) R S - Ef) cc (Measure.pi (fun _ : Fin M => Pζ)) :=
        { integrable_exp_mul := fun t => Lemma2Aux.int_exp _ hfm hfB t Ef
          mgf_le := fun t => by
            have h := Lemma2Aux.mgf_bound Pζ (2 * R / M) R (by positivity) M _ hfm hfB hbd t
            rw [← hEf] at h
            calc mgf (fun S => Lemma2Aux.fn (m := m) (M := M) R S - Ef) (Measure.pi (fun _ : Fin M => Pζ)) t
                = ∫ S, Real.exp (t * (Lemma2Aux.fn (m := m) (M := M) R S - Ef)) ∂(Measure.pi (fun _ : Fin M => Pζ)) := rfl
              _ ≤ Real.exp (M * ((2 * R / M) ^ 2 * t ^ 2 / 8)) := h
              _ = Real.exp (cc * t ^ 2 / 2) := by
                  rw [hcc]
                  congr 1
                  field_simp
                  ring }
      have hmeas := Hsg.measure_ge_le hε0
      have hexp : Real.exp (-ε ^ 2 / (2 * (cc : ℝ))) = δ := by
        have hRne : R ≠ 0 := hRpos.ne'
        rw [hcc, hε2, show -(R ^ 2 / M * (2 * Real.log (1 / δ))) / (2 * (R ^ 2 / M)) =
          -Real.log (1 / δ) by field_simp]
        rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
      refine ⟨{S | ε ≤ Lemma2Aux.fn (m := m) (M := M) R S - Ef}, ?_, fun S hS hSbad => ?_⟩
      · calc (Measure.pi (fun _ : Fin M => Pζ)) {S | ε ≤ Lemma2Aux.fn (m := m) (M := M) R S - Ef}
            = ENNReal.ofReal ((Measure.pi (fun _ : Fin M => Pζ)).real {S | ε ≤ Lemma2Aux.fn (m := m) (M := M) R S - Ef}) :=
              (ofReal_measureReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (hmeas.trans_eq hexp)
      · have hlt : Lemma2Aux.fn (m := m) (M := M) R S - Ef < ε := not_le.1 hSbad
        have hf0 : 0 ≤ Lemma2Aux.fn (m := m) (M := M) R S := norm_nonneg _
        have hq : 0 ≤ R / Real.sqrt M := by positivity
        have hle : Lemma2Aux.fn (m := m) (M := M) R S ≤
            R / Real.sqrt M * (2 + Real.sqrt (2 * Real.log (1 / δ))) := by
          have h : R / Real.sqrt M * (2 + Real.sqrt (2 * Real.log (1 / δ))) =
              2 * (R / Real.sqrt M) + ε := by rw [hε]; ring
          linarith
        rw [← Lemma2Aux.fn_sq S hS]
        calc Lemma2Aux.fn R S ^ 2
            ≤ (R / Real.sqrt M * (2 + Real.sqrt (2 * Real.log (1 / δ)))) ^ 2 :=
              pow_le_pow_left₀ hf0 hle 2
          _ = betaC M R δ := by
              rw [mul_pow, div_pow, Real.sq_sqrt hMpos.le]
              rfl
  obtain ⟨bad, hbad, hgood⟩ := key
  have hsub : {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}ᶜ ⊆
      bad ∪ {S | ¬ ∀ i, S i ⬝ᵥ S i ≤ R ^ 2} := by
    intro S hS
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    exact hS (hgood S (not_not.1 hcon.2) hcon.1)
  have hTc : (Measure.pi (fun _ : Fin M => Pζ)) {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}ᶜ ≤
      ENNReal.ofReal δ := by
    calc (Measure.pi (fun _ : Fin M => Pζ)) {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}ᶜ
        ≤ (Measure.pi (fun _ : Fin M => Pζ)) (bad ∪ {S | ¬ ∀ i, S i ⬝ᵥ S i ≤ R ^ 2}) := measure_mono hsub
      _ ≤ (Measure.pi (fun _ : Fin M => Pζ)) bad + (Measure.pi (fun _ : Fin M => Pζ)) {S | ¬ ∀ i, S i ⬝ᵥ S i ≤ R ^ 2} := measure_union_le _ _
      _ = (Measure.pi (fun _ : Fin M => Pζ)) bad := by rw [ae_iff.1 hA, add_zero]
      _ ≤ ENNReal.ofReal δ := hbad
  have h1 : (1 : ENNReal) ≤ (Measure.pi (fun _ : Fin M => Pζ)) {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ} +
      (Measure.pi (fun _ : Fin M => Pζ)) {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}ᶜ := by
    calc (1 : ENNReal) = (Measure.pi (fun _ : Fin M => Pζ)) Set.univ := measure_univ.symm
      _ = (Measure.pi (fun _ : Fin M => Pζ)) ({S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ} ∪
            {S : Fin M → (Fin m → ℝ) | empMean S ⬝ᵥ empMean S ≤ betaC M R δ}ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ _ := measure_union_le _ _
  rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one, tsub_le_iff_right]
  exact h1.trans (by gcongr)
