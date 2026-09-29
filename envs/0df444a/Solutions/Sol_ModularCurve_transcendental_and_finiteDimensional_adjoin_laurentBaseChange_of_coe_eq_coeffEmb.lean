-- Prove2me | solution 1 for ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f1d9d388-8cf4-5376-b3b8-3d67d43820b0

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve
open scoped TensorProduct

namespace CC2B01K4

variable (L : Type) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

private def emb : ↥F₀ →+* ↥(laurentBaseChange L F₀) :=
  ((coeffEmb L).comp (SubringClass.subtype F₀)).codRestrict (laurentBaseChange L F₀)
    fun x => coeffEmb_mem_laurentBaseChange L x.2

private theorem emb_apply (f : ↥F₀) :
    emb L F₀ f = ⟨coeffEmb L (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L f.2⟩ := rfl

private theorem emb_algebraMap (q : ℚ) :
    emb L F₀ (algebraMap ℚ ↥F₀ q) = algebraMap L ↥(laurentBaseChange L F₀) (algebraMap ℚ L q) :=
  RingHom.congr_fun (Subsingleton.elim ((emb L F₀).comp (algebraMap ℚ ↥F₀))
    ((algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap ℚ L))) q

private theorem emb_comp_algebraMap :
    (algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap ℚ L) =
      (emb L F₀).comp (algebraMap ℚ ↥F₀) :=
  RingHom.ext fun q => (emb_algebraMap L F₀ q).symm

private theorem emb_eq_baseChangeEquiv_one_tmul [Algebra.IsAlgebraic ℚ L] (f : ↥F₀) :
    emb L F₀ f = baseChangeEquiv L F₀ (1 ⊗ₜ f) :=
  (baseChangeEquiv_one_tmul L F₀ f).symm

private theorem transcendental_emb [Algebra.IsAlgebraic ℚ L] {j : ↥F₀} (hj : Transcendental ℚ j) :
    Transcendental L (emb L F₀ j) := by
  letI iQA : Algebra ℚ ↥(laurentBaseChange L F₀) :=
    ((algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap ℚ L)).toAlgebra
  haveI : @IsScalarTower ℚ L ↥(laurentBaseChange L F₀) _ _ iQA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hQ : Transcendental ℚ (emb L F₀ j) :=
    hj.ringHom_of_comp_eq (RingHom.id ℚ) (emb L F₀) Function.surjective_id (emb L F₀).injective
      (by
        refine RingHom.ext fun q => ?_
        change algebraMap ℚ ↥(laurentBaseChange L F₀) q = emb L F₀ (algebraMap ℚ ↥F₀ q)
        rw [emb_algebraMap]
        rfl)
  exact hQ.extendScalars L

private theorem span_range_one_tmul_eq_top (k K E : Type) [Field k] [Field K] [Algebra k K]
    [AddCommGroup E] [Module k E] :
    Submodule.span K (Set.range fun f : E => (1 : K) ⊗ₜ[k] f) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul c f =>
    have h : c ⊗ₜ[k] f = c • ((1 : K) ⊗ₜ[k] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

private theorem span_range_emb_eq_top [Algebra.IsAlgebraic ℚ L] :
    Submodule.span L (Set.range fun f : ↥F₀ => emb L F₀ f) = ⊤ := by
  have h := span_range_one_tmul_eq_top ℚ L ↥F₀
  apply_fun Submodule.map (baseChangeEquiv L F₀).toLinearEquiv.toLinearMap at h
  rw [Submodule.map_top, LinearEquiv.range, Submodule.map_span, ← Set.range_comp] at h
  convert h using 3 <;> try rfl
  funext f
  simp only [Function.comp_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    emb_eq_baseChangeEquiv_one_tmul]

private theorem emb_mem_adjoin {j f : ↥F₀} (hf : f ∈ IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) :
    emb L F₀ f ∈ IntermediateField.adjoin L ({emb L F₀ j} : Set ↥(laurentBaseChange L F₀)) := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hf ⊢
  obtain ⟨r, s, rfl⟩ := hf
  refine ⟨r.map (algebraMap ℚ L), s.map (algebraMap ℚ L), ?_⟩
  rw [map_div₀, Polynomial.map_aeval_eq_aeval_map (emb_comp_algebraMap L F₀),
    Polynomial.map_aeval_eq_aeval_map (emb_comp_algebraMap L F₀)]

private theorem finiteDimensional_adjoin_emb [Algebra.IsAlgebraic ℚ L] (j : ↥F₀)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀] :
    FiniteDimensional ↥(IntermediateField.adjoin L ({emb L F₀ j} : Set ↥(laurentBaseChange L F₀)))
      ↥(laurentBaseChange L F₀) := by
  classical
  set E := IntermediateField.adjoin L ({emb L F₀ j} : Set ↥(laurentBaseChange L F₀)) with hE
  let K := IntermediateField.adjoin ℚ ({j} : Set ↥F₀)
  let bK := Module.finBasis ↥K ↥F₀
  let W : Submodule ↥E ↥(laurentBaseChange L F₀) :=
    Submodule.span ↥E (Set.range fun i => emb L F₀ (bK i))

  have key : ∀ f : ↥F₀, emb L F₀ f ∈ W := by
    intro f
    rw [← bK.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have hc : emb L F₀ (algebraMap ↥K ↥F₀ (bK.repr f i)) ∈ E :=
      emb_mem_adjoin L F₀ (bK.repr f i).2
    have : emb L F₀ (algebraMap ↥K ↥F₀ (bK.repr f i)) * emb L F₀ (bK i) =
        (⟨_, hc⟩ : ↥E) • emb L F₀ (bK i) := by
      rw [Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have htop : W.restrictScalars L = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← span_range_emb_eq_top L F₀, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact key f
  have hW : W = ⊤ := Submodule.restrictScalars_injective L _ _ (by rw [htop, Submodule.restrictScalars_top])
  exact ⟨by rw [← hW]; exact Submodule.fg_span (Set.finite_range _)⟩

end CC2B01K4

theorem solution
    (L : Type) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) (hj : Transcendental ℚ j)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀]
    (jb : ↥(laurentBaseChange L F₀))
    (hjb : (jb : LaurentSeries L) = coeffEmb L ((j : ↥F₀) : LaurentSeries ℚ)) :
    Transcendental L jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin L ({jb} : Set ↥(laurentBaseChange L F₀)))
        ↥(laurentBaseChange L F₀) := by
  obtain rfl : jb = CC2B01K4.emb L F₀ j := Subtype.ext hjb
  exact ⟨CC2B01K4.transcendental_emb L F₀ hj, CC2B01K4.finiteDimensional_adjoin_emb L F₀ j⟩

end

end S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb (solution)
