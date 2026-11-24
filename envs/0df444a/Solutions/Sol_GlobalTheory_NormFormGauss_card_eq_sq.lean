-- Prove2me | solution 1 for GlobalTheory.NormFormGauss.card_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:49.174651+00:00
-- url     : https://prove2.me/submissions/4556f755-20e4-4ae6-aa24-b80a0a0048aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss
namespace GlobalTheory.NormFormGauss
theorem _root_.solution {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by
  let T : k →+ k := s.toAddMonoidHom - AddMonoidHom.id k
  have hT : ∀ x, T x = s x - x := fun x => rfl
  have h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [AddMonoidHom.mem_ker, hT, sub_eq_zero]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have h4 : Nat.card T.range = Nat.card T.ker := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)
    · have hu : s u = u := by
        have := u.2
        rw [AddMonoidHom.mem_ker, hT, sub_eq_zero] at this
        exact this
      rw [hT, map_mul, hu]; ring
    · intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (mul_left_cancel₀ hr this)
    · rintro ⟨_, t, rfl⟩
      refine ⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]
        field_simp
        ring
      · apply Subtype.ext
        simp only [hT]
        field_simp
  rw [← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]
end GlobalTheory.NormFormGauss
