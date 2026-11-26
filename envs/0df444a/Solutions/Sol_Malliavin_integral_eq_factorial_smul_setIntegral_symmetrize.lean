-- Prove2me | solution 1 for Malliavin.integral_eq_factorial_smul_setIntegral_symmetrize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:04.227287+00:00
-- url     : https://prove2.me/submissions/a072d601-928f-4dd3-8ec1-b8d06e21feb4

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_disjoint_sortedBy
import Theorems.Thm_Malliavin_iUnion_sortedBy_eq
import Theorems.Thm_Malliavin_measurableSet_sortedBy
import Theorems.Thm_Malliavin_measure_diagonal_eq_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



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
    {g : (Fin n → T) → E} (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hdiag : ((diagonal T n)ᶜ : Set (Fin n → T)) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (Set.univ : Set (Fin n → T)) := by
    rw [ae_eq_univ, compl_compl]
    exact measure_diagonal_eq_zero n
  -- each tile: `∫_{sortedBy σ} g = ∫_{Δₙ} g (u ∘ ⇑(σ⁻¹))`
  have htile : ∀ σ : Equiv.Perm (Fin n),
      ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) =
        ∫ u in simplex T n, g (u ∘ ⇑(σ⁻¹)) ∂(Measure.pi fun _ : Fin n => μ) := by
    intro σ
    have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ σ) :=
      (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl T)).measurableEmbedding
    refine Eq.trans ?_ ((measurePreserving_comp_perm μ n σ).setIntegral_preimage_emb hemb
      (fun u => g (u ∘ ⇑(σ⁻¹))) (simplex T n))
    refine setIntegral_congr_fun (measurableSet_sortedBy n σ) fun t _ => ?_
    congr 1
    ext i
    simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
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
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ u in simplex T n, g (u ∘ ⇑(σ⁻¹))
          ∂(Measure.pi fun _ : Fin n => μ) :=
        Finset.sum_congr rfl fun σ _ => htile σ
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ u in simplex T n, g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ) :=
        Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
          (fun σ => ∫ u in simplex T n, g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ))
    _ = ∫ u in simplex T n, ∑ σ : Equiv.Perm (Fin n), g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ) :=
        (integral_finsetSum _ fun σ _ =>
          (memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hint).comp_measurePreserving
            (measurePreserving_comp_perm μ n σ))).integrableOn).symm
    _ = n.factorial • ∫ t in simplex T n, symmetrize n g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        simp_rw [symmetrize_apply]
        rw [integral_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast n.factorial_ne_zero),
          one_smul]
end Malliavin
