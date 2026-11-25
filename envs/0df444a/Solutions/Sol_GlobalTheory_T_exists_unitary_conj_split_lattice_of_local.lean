-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_conj_split_lattice_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:27.665948+00:00
-- url     : https://prove2.me/submissions/fd7dd5af-d2b2-483f-b4bf-c4651a893e7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocalStatement
import Theorems.Thm_GlobalTheory_UTrans_exists_isU_conj_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  first | exact @GlobalTheory.UTrans.exists_isU_conj_mem | exact GlobalTheory.UTrans.exists_isU_conj_mem | (intros; apply GlobalTheory.UTrans.exists_isU_conj_mem <;> assumption)
end _root_.GlobalTheory.T
