-- Prove2me | solution 1 for MassDataIdxCore.latGL_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:28.374059+00:00
-- url     : https://prove2.me/submissions/f9f46067-07d5-4067-b7d2-9df181e62411

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
import Theorems.Thm_MassDataIdxCore_ker_fwd
import Theorems.Thm_MassDataIdxCore_psi_ker_iff
import Theorems.Thm_MassDataIdxCore_psi_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (hKB : KerBack O θ s J P) (hSU : SurjCore O θ s J P) (c : O) {H : Type} [Group H]
    (m : H →* GL n T) (hmU : ∀ h, m h ∈ Formalism.UG.UJ s J)
    (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)
    (hon : ∀ g : GL n T, g ∈ Formalism.UG.UJ s J → (∀ x, x ∈ Lat O θ J P ↔ (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) →
      ∃ h, m h = g) :
    ∃ ψ : H →* GL n O, Function.Surjective ψ ∧ ∀ h, (∀ i j, (((ψ h : GL n O) : Matrix n n O) - 1) i j ∈
      Ideal.span {c}) ↔
      ∀ y ∈ Lat O θ J P, ∃ z ∈ Lat O θ J P, (((m h : GL n T) : Matrix n n T) - 1) *ᵥ y = (c : K) • z := by
  refine ⟨psi O θ J P m hK, ?_, ?_⟩
  · intro A
    obtain ⟨g, hgU, hgL, hgA⟩ := hSU A
    obtain ⟨h, rfl⟩ := hon g hgU hgL
    refine ⟨h, Units.ext (map_inj O ?_)⟩
    simp only
    rw [psi_map, hgA]
  · intro h
    rw [psi_ker_iff]
    constructor
    · intro hw
      exact hKB (c : K) (m h) (hmU h) (hK h) hw
    · intro hl
      exact ker_fwd O θ J P (c : K) (m h) hl
end MassDataIdxCore
