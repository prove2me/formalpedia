-- Prove2me | solution 1 for Malliavin.setIntegral_sortedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:35.254876+00:00
-- url     : https://prove2.me/submissions/2d025d9b-ad51-434e-b8f9-45fc9425a1ac

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_measurableSet_sortedBy

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
theorem _root_.solution {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (σ : Equiv.Perm (Fin n)) :
    ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ σ) :=
    (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl T)).measurableEmbedding
  calc ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t in (fun t : Fin n → T => t ∘ σ) ⁻¹' simplex T n, g (t ∘ σ)
          ∂(Measure.pi fun _ : Fin n => μ) :=
        setIntegral_congr_fun (measurableSet_sortedBy n σ) fun t _ => (hg σ t).symm
    _ = ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        (measurePreserving_comp_perm μ n σ).setIntegral_preimage_emb hemb g _
end Malliavin
