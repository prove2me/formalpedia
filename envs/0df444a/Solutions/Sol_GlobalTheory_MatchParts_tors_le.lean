-- Prove2me | solution 1 for GlobalTheory.MatchParts.tors_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:28.736012+00:00
-- url     : https://prove2.me/submissions/682685ec-ce98-4455-941b-a6ba11f74a1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_P2M_GlobalTheory_MatchParts_tot__1edb3291971f
import Theorems.Thm_GlobalTheory_MatchParts_pow_eq_one_of
import Theorems.Thm_GlobalTheory_MatchParts_exists_rep
import Theorems.Thm_GlobalTheory_MatchParts_nsmul_cancel
import Theorems.Thm_GlobalTheory_MatchParts_card_le_of_rel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
namespace GlobalTheory.MatchParts
theorem _root_.solution (μ : Match N N' n) (hn : 1 < n) {k a a' : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N.InG p → N'.InG p')
    (e : Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin a → ZMod k)))
    (e' : Nonempty ((powMonoidHom k : N'.Gt →* N'.Gt).ker ≃* Multiplicative (Fin a' → ZMod k))) : a ≤ a' := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := e'
  have h1 : Nat.card (powMonoidHom k : N.Gt →* N.Gt).ker = k ^ a := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  have h2 : Nat.card (powMonoidHom k : N'.Gt →* N'.Gt).ker = k ^ a' := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  haveI : Finite (powMonoidHom k : N'.Gt →* N'.Gt).ker :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun x x' => μ.r k (ofG x.1 x.2) (ofG x'.1 x'.2)) (fun x => ?_) ?_
  · obtain ⟨p', h⟩ := tot' μ hl (ofG x.1 x.2)
    obtain ⟨q', e, h0⟩ := exists_rep (hG _ _ h ⟨0, by simp [ofG]⟩)
    refine ⟨⟨q'.1.2, pow_eq_one_of q' h0⟩, ?_⟩
    have : ofG q'.1.2 (pow_eq_one_of q' h0) = q' := Subtype.ext (Prod.ext h0.symm rfl)
    have h' := (r_right μ h).2 e
    rw [← this] at h'
    exact h'
  · intro x y b h h'
    obtain ⟨z, hz, hz'⟩ := μ.inj k _ _ _ h h'
    have : z = 0 := nsmul_cancel (a := k) (by omega) (by simpa [ofG] using hz.symm)
    rw [this, N.io_zero, mul_one] at hz'
    exact Subtype.ext hz'.symm
end GlobalTheory.MatchParts
