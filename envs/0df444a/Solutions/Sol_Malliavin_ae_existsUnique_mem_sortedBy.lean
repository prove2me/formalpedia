-- Prove2me | solution 1 for Malliavin.ae_existsUnique_mem_sortedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:53.81383+00:00
-- url     : https://prove2.me/submissions/5264daa2-6f1d-4319-ba86-2e345b4c54ff

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_exists_strictMono_comp_of_injective
import Theorems.Thm_Malliavin_perm_eq_of_strictMono_comp
import Theorems.Thm_Malliavin_ae_injective

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
theorem _root_.solution [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), ∃! σ : Equiv.Perm (Fin n), t ∈ sortedBy T n σ := by
  filter_upwards [ae_injective (μ := μ) n] with t ht
  obtain ⟨σ, hσ⟩ := exists_strictMono_comp_of_injective ht
  exact ⟨σ, hσ, fun τ hτ => perm_eq_of_strictMono_comp ht hτ hσ⟩
end Malliavin
