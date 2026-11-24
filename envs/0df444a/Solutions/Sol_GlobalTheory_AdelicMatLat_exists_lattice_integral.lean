-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.exists_lattice_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:51.122436+00:00
-- url     : https://prove2.me/submissions/af14b780-19f8-4c98-8cbb-9766b5bb6666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_isLattice_lat
import Theorems.Thm_GlobalTheory_AdelicMatLat_inv_mul_mem

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
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  intro E _ _ n β
  refine ⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩
  rw [Matrix.mul_apply]
  exact h1 i j v
end GlobalTheory.AdelicMatLat
