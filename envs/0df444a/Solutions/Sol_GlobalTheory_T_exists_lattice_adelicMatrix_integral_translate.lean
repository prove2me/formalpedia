-- Prove2me | solution 1 for GlobalTheory.T.exists_lattice_adelicMatrix_integral_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:52.2092+00:00
-- url     : https://prove2.me/submissions/015c4517-8a24-40bf-a4f6-1ae728773efd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslateStatement
import Theorems.Thm_GlobalTheory_AdelicMatLat_exists_lattice_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  first | exact @GlobalTheory.AdelicMatLat.exists_lattice_integral | exact GlobalTheory.AdelicMatLat.exists_lattice_integral | (intros; apply GlobalTheory.AdelicMatLat.exists_lattice_integral <;> assumption)
end _root_.GlobalTheory.T
