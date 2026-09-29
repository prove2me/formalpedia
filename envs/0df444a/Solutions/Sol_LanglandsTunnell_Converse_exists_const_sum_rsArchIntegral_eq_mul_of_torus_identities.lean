-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ebddd25b-3ea7-5845-afc5-78e9c2b88309

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Theorems.Thm_LanglandsTunnell_Converse_exists_const_rsArchIntegral_eq_mul_integral_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities

set_option autoImplicit false

noncomputable section

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "exists_const_rsArchIntegral_eq_mul_integral_diagonal"
namespace ArchAssembly
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section Borel

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel _
private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private def unipCoord (g : GL (Fin 2) ℝ) : ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1

private theorem unipCoord_unipotentGL2 (x : ℝ) : unipCoord (unipotentGL2 x) = x := by
  simp [unipCoord, unipotentGL2]

private theorem continuous_unipCoord : Continuous unipCoord := by
  unfold unipCoord
  exact Units.continuous_val.matrix_elem 0 1

private theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : ℝ → GL (Fin 2) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : ℝ => (!![(1 : ℝ), x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : ℝ => (!![(1 : ℝ), -x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem mem_realUnipotent_iff (g : GL (Fin 2) ℝ) :
    g ∈ realUnipotent ↔ g = unipotentGL2 (unipCoord g) := by
  constructor
  · rintro ⟨y, rfl⟩
    change unipotentGL2 (Multiplicative.toAdd y) =
      unipotentGL2 (unipCoord (unipotentGL2 (Multiplicative.toAdd y)))
    rw [unipCoord_unipotentGL2]
  · intro h
    exact ⟨Multiplicative.ofAdd (unipCoord g), by simpa [unipotentGL2Hom] using h.symm⟩

private def unitCell : Set realUnipotent :=
  {n : realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}

private def unipParam (x : ℝ) : realUnipotent :=
  ⟨unipotentGL2 x, (mem_realUnipotent_iff _).2 (by rw [unipCoord_unipotentGL2])⟩

private theorem continuous_unipParam : Continuous unipParam :=
  continuous_unipotentGL2.subtype_mk _

private theorem unitCell_subset_image : unitCell ⊆ unipParam '' Set.Icc (0 : ℝ) 1 := by
  intro n hn
  refine ⟨unipCoord n, hn, ?_⟩
  exact Subtype.ext ((mem_realUnipotent_iff _).1 n.2).symm

private theorem isOpen_openCell :
    IsOpen {n : realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Ioo (0 : ℝ) 1} :=
  isOpen_Ioo.preimage (continuous_unipCoord.comp continuous_subtype_val)

private theorem unitCell_measure_ne_zero (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    μN unitCell ≠ 0 := by
  have hsub : {n : realUnipotent | ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Ioo (0 : ℝ) 1} ⊆
      unitCell := fun n hn => Set.Ioo_subset_Icc_self hn
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
  refine isOpen_openCell.measure_pos μN ⟨unipParam (1 / 2), ?_⟩
  show unipCoord (unipotentGL2 (1 / 2)) ∈ Set.Ioo (0 : ℝ) 1
  rw [unipCoord_unipotentGL2]
  constructor <;> norm_num

private theorem unitCell_measure_ne_top (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    μN unitCell ≠ ⊤ :=
  (lt_of_le_of_lt (measure_mono unitCell_subset_image)
    (isCompact_Icc.image continuous_unipParam).measure_lt_top).ne

private theorem unitCell_toReal_pos (μN : Measure realUnipotent) [μN.IsHaarMeasure] :
    0 < (μN {n : realUnipotent |
      ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal :=
  ENNReal.toReal_pos (unitCell_measure_ne_zero μN) (unitCell_measure_ne_top μN)

end Borel

end LanglandsTunnell.Converse.ArchAssembly
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell.Converse.ArchAssembly"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell.Converse"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell"

theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (coef : Fin n → ℂ)
      (W F Wd Fd : Fin n → GL (Fin 2) ℝ → ℂ) (Γ Γd e ed : ℂ → ℂ) (ε : ℂ) (σ₀ : ℝ)
      (_hN : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        W i (u * g) * F i (u * g) = W i g * F i g)
      (_hNd : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        Wd i (u * g) * Fd i (u * g) = Wd i g * Fd i g)
      (_hK : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, W i (g * k) * F i (g * k) = W i g * F i g)
      (_hKd : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, Wd i (g * k) * Fd i (g * k) = Wd i g * Fd i g)
      (_hmeas : ∀ i, Measurable (W i) ∧ Measurable (F i) ∧ Measurable (Wd i) ∧ Measurable (Fd i))
      (_hint : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (W i g * F i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hintd : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (Wd i g * Fd i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hvec : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W i p * F i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = e s * Γ s)
      (_hpair : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((Wd i p * Fd i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = ed s * Γd s)
      (_hfe : ∀ s : ℂ, ed s = ε * e (1 - s)),
      (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (W i) (F i) = (c : ℂ) * (e s * Γ s)) ∧
        (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (Wd i) (Fd i) =
            (c : ℂ) * (ed s * Γd s)) ∧
        (∀ s : ℂ, (c : ℂ) * ed s = ε * ((c : ℂ) * e (1 - s))) := by
  intro hHaar μN instN
  obtain ⟨c₀, hc₀, hGT⟩ :=
    LanglandsTunnell.Converse.exists_const_rsArchIntegral_eq_mul_integral_diagonal hHaar
  have hκ : 0 < (μN {n : realUnipotent |
      ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal :=
    LanglandsTunnell.Converse.ArchAssembly.unitCell_toReal_pos μN
  refine ⟨c₀ / (μN {n : realUnipotent |
      ((n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ∈ Set.Icc (0 : ℝ) 1}).toReal, div_pos hc₀ hκ, ?_⟩
  intro n coef W F Wd Fd Γ Γd e ed ε σ₀ hN hNd hK hKd hmeas hint hintd hvec hpair hfe
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · rw [← hvec s hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGT μN s (W i) (F i) (hN i) (hK i) (hmeas i).1 (hmeas i).2.1 (hint i s hs)]
    ring
  · rw [← hpair s hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hGT μN s (Wd i) (Fd i) (hNd i) (hKd i) (hmeas i).2.2.1 (hmeas i).2.2.2 (hintd i s hs)]
    ring
  · rw [hfe s]
    ring

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.LanglandsTunnell.Converse.ArchAssembly"

end S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities (solution)
