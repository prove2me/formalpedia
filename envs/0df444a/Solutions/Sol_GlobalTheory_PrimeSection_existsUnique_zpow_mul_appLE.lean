-- Prove2me | solution 1 for GlobalTheory.PrimeSection.existsUnique_zpow_mul_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:10.684492+00:00
-- url     : https://prove2.me/submissions/817d17ba-cda1-4c54-8753-ec6074dc8152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_exists_transport
import Theorems.Thm_GlobalTheory_PrimeSection_existsUnique_zpow_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)
include hη hp hj
namespace GlobalTheory.PrimeSection
theorem _root_.solution (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  obtain ⟨r', τ', hτ', hr', h0, -, H⟩ := exists_transport hj hW r hr τ hτ
  simpa only [H] using existsUnique_zpow_mul hη hp hU hg τ' hτ' hr'
    (hr0.imp fun a ha h ↦ ha (h0 a h))
end GlobalTheory.PrimeSection
