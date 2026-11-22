-- Prove2me | solution 1 for MeasureTheory.lintegral_fin_nat_prod_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:58.991916+00:00
-- url     : https://prove2.me/submissions/f2ea212b-9382-42ab-896e-81d9fec4ba47

module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory
open scoped ENNReal
open MeasureTheory
variable {ι : Type*} [Fintype ι]
set_option backward.isDefEq.respectTransparency false
namespace MeasureTheory
theorem _root_.solution {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      -- Split off coordinate 0 via the measure-preserving equiv `ℝ^{n+1} ≃ ℝ × ℝ^n`.
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      -- Now: ∫⁻ (x : E 0 × …), f 0 x.1 * ∏ i, f i.succ (x.2 i). Factor by Tonelli.
      have hmul := lintegral_prod_mul (μ := μ 0) (ν := Measure.pi fun j => μ j.succ)
        (f := f 0) (g := fun y : (j : Fin n) → E j.succ => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        ((Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))).aemeasurable)
      -- `hmul : LHS = (∫⁻ f 0) * ∫⁻ ∏ f i.succ`; close by IH + `Fin.prod_univ_succ`.
      rw [n_ih (fun i => f i.succ) (fun i => hf _)] at hmul
      exact hmul
end MeasureTheory
