-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltAutHom_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:56.667314+00:00
-- url     : https://prove2.me/submissions/370575f2-85c9-4dd0-9540-5356909b4160

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_untiltAutHom_injective
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_untiltField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] :
    Function.Bijective (untiltAutHom (K := K) (C := C) (p := p) N) ∧
      IsGalois K (untiltField K C p N) := by
  have hinj := untiltAutHom_injective (K := K) (C := C) (p := p) N
  have h1 : Nat.card (N ≃ₐ[K♭] N) = Module.finrank K (untiltField K C p N) := by
    rw [IsGalois.card_aut_eq_finrank, finrank_untiltField]
  have h2 : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) ≤
      Module.finrank K (untiltField K C p N) := by
    refine le_trans ?_ (card_algHom_le_finrank K (untiltField K C p N) (untiltField K C p N))
    exact Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
  have h3 : Nat.card (N ≃ₐ[K♭] N) ≤
      Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) :=
    Nat.card_le_card_of_injective _ hinj
  have heq : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) =
      Module.finrank K (untiltField K C p N) := le_antisymm h2 (h1 ▸ h3)
  exact ⟨hinj.bijective_of_nat_card_le (by rw [heq, h1]), IsGalois.of_card_aut_eq_finrank _ _ heq⟩
end GroundTheory.PAdicHodge
