-- Prove2me | solution 1 for GlobalTheory.CapelliLocality.foldr_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:12.329014+00:00
-- url     : https://prove2.me/submissions/82d01d38-b752-4a78-bf29-9095b0591613

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CapelliOperatorUnitaryGroupLocal
import Theorems.Thm_GlobalTheory_CapelliLocality_rdV_congr
import Theorems.Thm_GlobalTheory_CapelliLocality_hpart1_mem
import Theorems.Thm_GlobalTheory_CapelliLocality_hpart2_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CapelliLocality
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CapelliLocality
theorem _root_.solution (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]
end GlobalTheory.CapelliLocality
