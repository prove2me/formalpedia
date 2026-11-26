-- Prove2me | solution 1 for Malliavin.integral_eq_factorial_smul_setIntegral_simplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:10.764867+00:00
-- url     : https://prove2.me/submissions/9ea8108f-24c5-4dbf-a84b-4177b4a9f2e7

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_disjoint_sortedBy
import Theorems.Thm_Malliavin_iUnion_sortedBy_eq
import Theorems.Thm_Malliavin_measurableSet_sortedBy
import Theorems.Thm_Malliavin_measure_diagonal_eq_zero
import Theorems.Thm_Malliavin_setIntegral_sortedBy

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [NullSingletonClass μ] {n : ℕ}
    {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hdiag : ((diagonal T n)ᶜ : Set (Fin n → T)) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (Set.univ : Set (Fin n → T)) := by
    rw [ae_eq_univ, compl_compl]
    exact measure_diagonal_eq_zero n
  calc ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t in (diagonal T n)ᶜ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [setIntegral_congr_set hdiag, Measure.restrict_univ]
    _ = ∫ t in ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [iUnion_sortedBy_eq]
    _ = ∑' σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        integral_iUnion (measurableSet_sortedBy n) (fun _ _ hστ => disjoint_sortedBy hστ)
          hint.integrableOn
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        tsum_fintype _
    _ = ∑ _σ : Equiv.Perm (Fin n), ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        Finset.sum_congr rfl fun σ _ => setIntegral_sortedBy hg σ
    _ = n.factorial • ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
end Malliavin
