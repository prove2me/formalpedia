-- Prove2me | solution 1 for GlobalTheory.PBasis.indep_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:17:30.377879+00:00
-- url     : https://prove2.me/submissions/8ca3dc96-633b-4992-8959-a6708de983f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GraphRingMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory GlobalTheory.PBasis
variable {k : Type} [Field k]
namespace GlobalTheory.PBasis
theorem _root_.solution {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) : Indep p (∅ : Set k) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g _ z hz h1
  have : graphRing p f g ∅ ≤ ((frobenius k p).prod f).range := by
    unfold graphRing
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, _⟩)
    · exact ⟨x, by simp [frobenius_def]⟩
    · exact hx.elim
  obtain ⟨x, rfl⟩ := this hz
  have hx : x ^ p = 0 := by simpa [frobenius_def] using h1
  have : x = 0 := pow_eq_zero_iff hp.ne_zero |>.1 hx
  simp [this]
end GlobalTheory.PBasis
