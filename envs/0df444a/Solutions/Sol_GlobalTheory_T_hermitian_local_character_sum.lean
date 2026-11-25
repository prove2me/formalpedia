-- Prove2me | solution 1 for GlobalTheory.T.hermitian_local_character_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:21.661886+00:00
-- url     : https://prove2.me/submissions/8565693c-c7d6-48b5-a4ab-330b1b731b90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSumStatement
import Theorems.Thm_GlobalTheory_HL_DivisibleGauss_share_and_gauss_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (π : E) (j N : ℕ), π ∈ L.O → π * L.cj π = algebraMap F E ((ϖ : F) ^ j) → (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ((R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) ∧ ∀ (i : ℕ), i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R.filter (fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c), ψ (t * nrm u)‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) := by
  first | exact @GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | exact GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | (intros; apply GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum <;> assumption)
end _root_.GlobalTheory.T
