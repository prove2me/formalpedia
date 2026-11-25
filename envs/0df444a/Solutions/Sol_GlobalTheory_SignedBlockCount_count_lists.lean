-- Prove2me | solution 1 for GlobalTheory.SignedBlockCount.count_lists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:57.821189+00:00
-- url     : https://prove2.me/submissions/1a4f8d2d-e4f3-40c4-9f80-0522aa09ef35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_lt
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_add
import Theorems.Thm_GlobalTheory_SignedBlockCount_sign_ne
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_self
import Theorems.Thm_GlobalTheory_SignedBlockCount_minor_self_ne
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.SignedBlockCount
open Formalism.MainNotions.S.Loc
variable {K : Type} [Field K]
namespace GlobalTheory.SignedBlockCount
theorem _root_.solution (n : ℕ) : ∀ η : ℕ → K, ∃ T : Finset (List (Kˣ × ℕ+)), T.card ≤ 2 ^ n ∧
    ∀ bs : List (Kˣ × ℕ+), (bs.map (fun b => (b.2 : ℕ))).sum = n →
      (∀ l ≤ n, minor bs l = η l) → bs ∈ T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro η
  by_cases hex : ∃ (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)),
      (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum = n ∧ ∀ l ≤ n, minor ((t, s) :: bs) l = η l
  · obtain ⟨t₀, s, bs₀, hs, h₀⟩ := hex
    have hsp := s.pos
    obtain ⟨T, hT, hT'⟩ := ih (n - s) (by omega) (fun l => η (s + l) / η s)
    let c : K := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ)
    have hc : c ≠ 0 := sign_ne _
    let R := (Polynomial.nthRoots s (η s / c)).toFinset
    have hR : R.card ≤ s := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
    refine ⟨Finset.image₂ (fun x bs => ((if h : x = 0 then 1 else Units.mk0 x h), s) :: bs) R T,
      ?_, ?_⟩
    · refine (Finset.card_image₂_le _ _ _).trans ?_
      calc R.card * T.card ≤ 2 ^ (s : ℕ) * 2 ^ (n - s) :=
            Nat.mul_le_mul (hR.trans (Nat.lt_two_pow_self).le) hT
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    · rintro (_ | ⟨⟨t, s'⟩, bs⟩) hsum h
      · simp only [List.map_nil, List.sum_nil] at hsum
        omega
      simp only [List.map_cons, List.sum_cons] at hsum
      have hsp' := s'.pos
      have e : s' = s := by
        apply PNat.eq
        rcases lt_trichotomy (s' : ℕ) s with h1 | h1 | h1
        · exact absurd ((h s' (by omega)).trans ((h₀ s' (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp' h1))) (minor_self_ne _ _ _)
        · exact h1
        · exact absurd ((h₀ s (by omega)).trans ((h s (by omega)).symm.trans
            (minor_lt _ _ _ _ hsp h1))) (minor_self_ne _ _ _)
      subst e
      have h1 := h s' (by omega)
      refine Finset.mem_image₂.2 ⟨t, ?_, bs, hT' bs (by omega) fun l hl => ?_, ?_⟩
      · simp only [R, Multiset.mem_toFinset, Polynomial.mem_nthRoots hsp]
        rw [← h1, minor_self, eq_div_iff hc, mul_comm]
      · rw [← h _ (by omega), ← h1, minor_add, ← minor_self t s' bs,
          mul_div_cancel_left₀ _ (minor_self_ne _ _ _)]
      · simp [t.ne_zero]
  · refine ⟨{[]}, by simpa using Nat.one_le_two_pow, ?_⟩
    rintro (_ | ⟨⟨t, s⟩, bs⟩) hsum h
    · simp
    · exact absurd ⟨t, s, bs, by simpa using hsum, h⟩ hex
end GlobalTheory.SignedBlockCount
