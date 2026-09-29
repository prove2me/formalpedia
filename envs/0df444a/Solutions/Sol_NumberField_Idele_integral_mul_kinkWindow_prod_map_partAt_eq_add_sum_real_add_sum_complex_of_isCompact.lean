-- Prove2me | solution 1 for NumberField.Idele.integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/892fc315-fb53-5826-a849-f0f07cf908f5

import Mathlib
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing Idele.partAt AdelicLevel.archEval AdeleRing.unitIdelesOutside Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt"
namespace Idele
p2m_export "NumberField.Idele" "partAt integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt"
namespace KinkFoldAux
p2m_open "NumberField.Idele NumberField"

open MeasureTheory

theorem integral_mul_add_sum_add_sum_mul {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} (R Cx : Finset ι)
    (ξf Pf Bf : α → ℂ) (Cf Ef : ι → α → ℂ) (ac bc : ι → ℂ)
    (hB : Integrable (fun z => ξf z * (Bf z * Pf z)) μ)
    (hC : ∀ w ∈ R, Integrable (fun z => ξf z * (Cf w z * Pf z)) μ)
    (hE : ∀ w ∈ Cx, Integrable (fun z => ξf z * (Ef w z * Pf z)) μ) :
    ∫ z, ξf z * ((Bf z + ∑ w ∈ R, ac w * Cf w z + ∑ w ∈ Cx, bc w * Ef w z) * Pf z) ∂μ =
      ∫ z, ξf z * (Bf z * Pf z) ∂μ +
      ∑ w ∈ R, ac w * ∫ z, ξf z * (Cf w z * Pf z) ∂μ +
      ∑ w ∈ Cx, bc w * ∫ z, ξf z * (Ef w z * Pf z) ∂μ := by
  have hpt : ∀ z, ξf z * ((Bf z + ∑ w ∈ R, ac w * Cf w z + ∑ w ∈ Cx, bc w * Ef w z) * Pf z) =
      ξf z * (Bf z * Pf z) + (∑ w ∈ R, ac w * (ξf z * (Cf w z * Pf z))) +
        ∑ w ∈ Cx, bc w * (ξf z * (Ef w z * Pf z)) := by
    intro z
    rw [add_mul, add_mul, mul_add, mul_add, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun w _ => by ring
    · exact Finset.sum_congr rfl fun w _ => by ring
  have hC' : ∀ w ∈ R, Integrable (fun z => ac w * (ξf z * (Cf w z * Pf z))) μ := fun w hw => (hC w hw).const_mul _
  have hE' : ∀ w ∈ Cx, Integrable (fun z => bc w * (ξf z * (Ef w z * Pf z))) μ := fun w hw => (hE w hw).const_mul _
  have hSC : Integrable (fun z => ∑ w ∈ R, ac w * (ξf z * (Cf w z * Pf z))) μ := integrable_finsetSum _ hC'
  have hSE : Integrable (fun z => ∑ w ∈ Cx, bc w * (ξf z * (Ef w z * Pf z))) μ := integrable_finsetSum _ hE'
  have hfg : Integrable (fun z => ξf z * (Bf z * Pf z) + ∑ w ∈ R, ac w * (ξf z * (Cf w z * Pf z))) μ := hB.add hSC
  simp_rw [hpt]
  rw [integral_add hfg hSE, integral_add hB hSC, integral_finsetSum _ hC', integral_finsetSum _ hE']
  simp_rw [integral_const_mul]

end NumberField.Idele.KinkFoldAux

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing Idele.partAt AdelicLevel.archEval AdeleRing.unitIdelesOutside Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt"
namespace Idele
p2m_export "NumberField.Idele" "partAt integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt"
namespace KinkFoldAux
p2m_open "NumberField.Idele NumberField"

theorem contDiff_vecCons_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : (Fin 2 → E) → ℂ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : E × E => B ![q.1, q.2]) := by
  refine hB.comp ?_
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simpa using contDiff_fst
  · simpa using contDiff_snd

theorem hasCompactSupport_vecCons_two {E : Type*} [TopologicalSpace E]
    {B : (Fin 2 → E) → ℂ} (hB : HasCompactSupport B) :
    HasCompactSupport (fun q : E × E => B ![q.1, q.2]) := by
  have h := hB.comp_homeomorph (Homeomorph.piFinTwo fun _ : Fin 2 => E).symm
  convert h using 1
  rfl

end NumberField.Idele.KinkFoldAux

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (B : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (C E : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport B)
    (hC : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w) ∧ HasCompactSupport (C w))
    (hE : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w) ∧ HasCompactSupport (E w))
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (h0 : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :
    (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((fun p : Fin 2 → mixedEmbedding.mixedSpace K =>
            B p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * C w p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * E w p) ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
      (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (B ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
      ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) *
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (C w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) +
      ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
        ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) *
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          (E w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K S)
            (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by
  classical

  have hIB := (NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt K ν S (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc
    (fun q : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => B ![q.1, q.2])
    (NumberField.Idele.KinkFoldAux.contDiff_vecCons_two hB.1) (NumberField.Idele.KinkFoldAux.hasCompactSupport_vecCons_two hB.2)
    Ca hCa (fun x y h => by
      simpa only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one, RingEquiv.symm_apply_apply] using
        h0 ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K y] (Or.inl h)) Φf hΦf b).1 x
  have hIC : ∀ w : NumberField.InfinitePlace K, Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ =>
      ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * (C w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] * ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) (Measure.map (NumberField.Idele.partAt K S)
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ))) :=
    fun w => (NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt K ν S (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc
      (fun q : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => C w ![q.1, q.2])
      (NumberField.Idele.KinkFoldAux.contDiff_vecCons_two (hC w).1) (NumberField.Idele.KinkFoldAux.hasCompactSupport_vecCons_two (hC w).2)
      Ca hCa (fun x y h => by
      simpa only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one, RingEquiv.symm_apply_apply] using
        h0 ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K y] (Or.inr ⟨w, Or.inl h⟩)) Φf hΦf b).1 x
  have hIE : ∀ w : NumberField.InfinitePlace K, Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ =>
      ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * (E w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] * ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) (Measure.map (NumberField.Idele.partAt K S)
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ))) :=
    fun w => (NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt K ν S (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc
      (fun q : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K => E w ![q.1, q.2])
      (NumberField.Idele.KinkFoldAux.contDiff_vecCons_two (hE w).1) (NumberField.Idele.KinkFoldAux.hasCompactSupport_vecCons_two (hE w).2)
      Ca hCa (fun x y h => by
      simpa only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one, RingEquiv.symm_apply_apply] using
        h0 ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K y] (Or.inr ⟨w, Or.inr h⟩)) Φf hΦf b).1 x
  simp only [Matrix.cons_val_zero]
  exact NumberField.Idele.KinkFoldAux.integral_mul_add_sum_add_sum_mul (Measure.map (NumberField.Idele.partAt K S)
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))
    (Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal))
    (Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex))
    (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ))
    (fun zS : (AdeleRing (𝓞 K) K)ˣ => ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
    (fun zS : (AdeleRing (𝓞 K) K)ˣ => B ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1])
    (fun w (zS : (AdeleRing (𝓞 K) K)ˣ) => C w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1])
    (fun w (zS : (AdeleRing (𝓞 K) K)ˣ) => E w ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1])
    (fun w => ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ))
    (fun w => ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ ^ 2 *
      Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ))
    hIB (fun w _ => hIC w) (fun w _ => hIE w)

end S_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
end P2MW
export P2MW.S_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact (solution)
