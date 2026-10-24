-- Prove2me | solution 1 for OAI.Problem315.switch_chain_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:16:42.563983+00:00
-- url     : https://prove2.me/submissions/7e52c7c3-dd52-4a62-9f07-d8596fc13363

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002
import Theorems.Thm_OAI_Problem315_PairEquality_actual_named_interaction
import Theorems.Thm_OAI_Problem315_PairResampling_spectralGap_of_triples_and_disjoint
import Theorems.Thm_OAI_Problem315_PairResampling_tripleGenerator_square
import Theorems.Thm_OAI_Problem315_SliceNormalized_reindexed_projection_energy_le_swap_sum

section
-- module Solutions.OAIQW_Problem315.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

theorem validSwitch_of_result_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_eq_reverse_of_ne {n : Nat} {G H : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hne : G ≠ H) (h : proposalResult G p = H) :
    proposalResult H (reverseProposal p) = G := by
  have hv : validSwitch G p := validSwitch_of_result_ne (by
    rw [h]
    exact Ne.symm hne)
  rw [← h]
  exact proposalResult_reverse hv

theorem switchKernel_symm {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    switchKernel n d G H = switchKernel n d H G := by
  classical
  by_cases hGH : G = H
  · subst H
    rfl
  have hvGH : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hc : ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card =
      ((allProposals n).filter (fun p => proposalResult H.val p = G.val)).card := by
    apply Finset.card_bij (fun p _ => reverseProposal p)
    · intro p hp
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne hvGH hp
    · intro p hp q hq heq
      have heq' := congrArg reverseProposal heq
      simpa using heq'
    · intro p hp
      refine ⟨reverseProposal p, ?_, reverseProposal_reverse p⟩
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne (Ne.symm hvGH) hp
  simp only [switchKernel, hGH, Ne.symm hGH, ↓reduceIte, zero_add, hc]

theorem switchKernel_nonneg {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    0 ≤ switchKernel n d G H := by
  classical
  unfold switchKernel
  positivity

theorem switchKernel_self_ge_half {n : Nat} {d : Fin n → Nat} (G : GraphState n d) :
    (1 : ℝ) / 2 ≤ switchKernel n d G G := by
  classical
  simp only [switchKernel, ↓reduceIte]
  exact le_add_of_nonneg_right (by positivity)

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FourVertexSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

theorem validSwitch_fourVertexProposal_iff {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d) :
    validSwitch G (fourVertexProposal a b c d h) ↔
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d := by
  constructor
  · intro hv
    refine ⟨hv.1 ?_, hv.1 ?_, hv.2 ?_, hv.2 ?_⟩ <;> simp
  · rintro ⟨hab, hcd, hac, hbd⟩
    constructor
    · intro u v huv
      rw [removedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact G.symm.symm _ _ hab
      · exact hcd
      · exact G.symm.symm _ _ hcd
    · intro u v huv
      rw [addedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hac
      · exact fun he => hac (G.symm.symm _ _ he)
      · exact hbd
      · exact fun he => hbd (G.symm.symm _ _ he)

theorem proposalResult_fourVertex_adj {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (u v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔
      (G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        (u = c ∧ v = d) ∨ (u = d ∧ v = c))) ∨
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  classical
  have hv : validSwitch G (fourVertexProposal a b c d h) :=
    (validSwitch_fourVertexProposal_iff G a b c d h).2 ⟨hab, hcd, hac, hbd⟩
  simp only [proposalResult, ite_eq_left hv, replaceEdges,
    removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem proposalResult_fourVertex_adj_first {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj a v ↔
      (G.Adj a v ∧ v ≠ b) ∨ v = c := by
  simpa [h.1, h.2.1, h.2.2.1] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd a v

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

private theorem involution_fin_four_card :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) = 3 := by
  decide

 theorem involution_card_of_card_four {V : Type*} [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (FixedPointFreeInvolution V) = 3 := by
  classical
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hV
  rw [Nat.card_congr (involutionCongr e), Nat.card_eq_fintype_card]
  exact involution_fin_four_card

variable {n : ℕ} {S : FourSet n}

theorem perfectMatching_card (S : FourSet n) : Nat.card (PerfectMatching S) = 3 := by
  rw [Nat.card_congr (matchingEquivInvolution S)]
  apply involution_card_of_card_four
  simpa only [Fintype.card_coe] using S.property

theorem orderedMatchings_card (S : FourSet n) :
    Nat.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun p : PerfectMatching S × PerfectMatching S => p.1 ≠ p.2) =
      (Finset.univ : Finset (PerfectMatching S)).offDiag := by
    ext p
    simp
  rw [hfilter, Finset.offDiag_card, Finset.card_univ]
  have hcard : Fintype.card (PerfectMatching S) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact perfectMatching_card S
  rw [hcard]

theorem fourSet_card (n : ℕ) : Nat.card (FourSet n) = n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem switchProposal_card (n : ℕ) : Nat.card (SwitchProposal n) = 6 * n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hcard (S : FourSet n) :
      Fintype.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact orderedMatchings_card S
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    fourSet_card, Nat.mul_comm]

theorem allProposals_card (n : ℕ) : (allProposals n).card = 6 * n.choose 4 := by
  classical
  unfold allProposals
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact switchProposal_card n

end Problem315.MatchingCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.KernelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

theorem proposal_fiber_cards_sum {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card) =
      (allProposals n).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (allProposals n) (allGraphStates n d) (proposalState G)
  have hf (H : GraphState n d) :
      ((allProposals n).filter (fun p => proposalState G p = H)) =
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact Subtype.ext_iff
  simp_rw [hf] at h
  simpa only [allGraphStates, Finset.mem_univ, Finset.filter_true] using h

theorem switchKernel_row_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  classical
  have hc : (Nat.choose n 4 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  unfold switchKernel
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum,
    proposal_fiber_cards_sum, MatchingCount.allProposals_card]
  have hdiag : (∑ H ∈ allGraphStates n d, if G = H then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    simp [allGraphStates]
  rw [hdiag]
  push_cast
  field_simp
  ring

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProposalUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Problem315

theorem IsPerfectMatchingOn.mem_iff_exists_adj {n : Nat} {S : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hm : IsPerfectMatchingOn S M) (v : Fin n) :
    v ∈ S ↔ ∃ w, M.Adj v w := by
  constructor
  · intro hv
    obtain ⟨w, hw, _⟩ := (hm v).1 hv
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    by_contra hv
    exact (hm v).2 hv w hw

theorem IsPerfectMatchingOn.support_unique {n : Nat} {S T : Finset (Fin n)}
    {M : SimpleGraph (Fin n)} (hS : IsPerfectMatchingOn S M)
    (hT : IsPerfectMatchingOn T M) : S = T := by
  ext v
  rw [hS.mem_iff_exists_adj v, hT.mem_iff_exists_adj v]

theorem SwitchProposal.ext_matchings {n : Nat} {p q : SwitchProposal n}
    (hM : removedMatching p = removedMatching q)
    (hN : addedMatching p = addedMatching q) : p = q := by
  rcases p with ⟨⟨S, hS⟩, ⟨⟨⟨M, hm⟩, ⟨N, hn⟩⟩, hmn⟩⟩
  rcases q with ⟨⟨T, hT⟩, ⟨⟨⟨M', hm'⟩, ⟨N', hn'⟩⟩, hmn'⟩⟩
  change M = M' at hM
  change N = N' at hN
  subst M'
  subst N'
  have hST : S = T := hm.support_unique hm'
  subst T
  rfl

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.OrthogonalPairResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

theorem state_inner (f g : StateSpace n d) :
    ⟪f, g⟫ = ∑ G : GraphState n d, f G * g G := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem constant_mem (c : ℝ) :
    WithLp.toLp 2 (fun _ : GraphState n d => c) ∈ fiberSpace n d a := by
  intro G H h
  rfl

theorem fiberStates_nonempty (G : GraphState n d) : (fiberStates a G).Nonempty :=
  ⟨G, self_mem_fiberStates a G⟩

theorem fiberIndicator_mem (G : GraphState n d) :
    fiberIndicator a G ∈ fiberSpace n d a := by
  intro H K hHK
  change (if SameFiber a G.val H.val then (1 : ℝ) else 0) =
    if SameFiber a G.val K.val then 1 else 0
  have hi : SameFiber a G.val H.val ↔ SameFiber a G.val K.val :=
    ⟨fun h => h.trans hHK, fun h => h.trans hHK.symm⟩
  simp only [hi]

theorem expectation_eq_average (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a f G = (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card := by
  have horth := Submodule.starProjection_inner_eq_zero (K := fiberSpace n d a)
    f (fiberIndicator a G) (fiberIndicator_mem a G)
  change ⟪f - expectation n d a f, fiberIndicator a G⟫ = 0 at horth
  rw [state_inner] at horth
  have hsum : (∑ H ∈ fiberStates a G, (f H - expectation n d a f H)) = 0 := by
    calc
      _ = ∑ H : GraphState n d, (f - expectation n d a f) H * fiberIndicator a G H := by
        unfold fiberStates
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases h : SameFiber a G.val H.val <;> simp [fiberIndicator, h]
      _ = 0 := horth
  have hequal : ∀ H ∈ fiberStates a G, expectation n d a f H = expectation n d a f G := by
    intro H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  have hsconst : (∑ H ∈ fiberStates a G, expectation n d a f H) =
      (fiberStates a G).card * expectation n d a f G := by
    calc
      _ = ∑ _H ∈ fiberStates a G, expectation n d a f G := Finset.sum_congr rfl hequal
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsconst] at hsum
  have hcard : (0 : ℝ) < (fiberStates a G).card := by
    exact_mod_cast Finset.card_pos.mpr (fiberStates_nonempty a G)
  apply (eq_div_iff (ne_of_gt hcard)).mpr
  linarith

end PairResampling
end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossTogglePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

open SwitchFlip

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem crossProposal_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    crossProposal j i k l h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
    tauto

theorem crossProposal_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    crossProposal i j l k h' = reverseProposal (crossProposal i j k l h) := by
  apply SwitchProposal.ext_matchings
  · ext u v
    simp only [crossProposal, removedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]
  · ext u v
    simp only [crossProposal, addedMatching_reverse,
      removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem crossProjection_swap_left (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct j i k l) :
    projection (d := d) (crossProposal j i k l h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_left i j k l h h', projection_reverse]

theorem crossProjection_swap_right (i j k l : Fin n)
    (h : FourDistinct i j k l) (h' : FourDistinct i j l k) :
    projection (d := d) (crossProposal i j l k h') =
      projection (crossProposal i j k l h) := by
  rw [crossProposal_swap_right i j k l h h', projection_reverse]

theorem endpoints_cases (a : VertexPair n) (i j : Fin n) (h : a.val = {i, j}) :
    (first a = i ∧ second a = j) ∨ (first a = j ∧ second a = i) := by
  have hf : first a = i ∨ first a = j := by
    have hm : first a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  have hs : second a = i ∨ second a = j := by
    have hm : second a ∈ a.val := by rw [pair_eq]; simp
    simpa only [h, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact False.elim (first_ne_second a (hf.trans hs.symm))
  · exact Or.inl ⟨hf, hs⟩
  · exact Or.inr ⟨hf, hs⟩
  · exact False.elim (first_ne_second a (hf.trans hs.symm))

theorem pairProjection_of_disjoint (a b : VertexPair n) (h : Disjoint a.val b.val) :
    pairProjection (d := d) a b = projection (pairProposal a b h) := by
  simp [pairProjection, h]

theorem pairProjection_eq_explicit (a b : VertexPair n)
    (h : Disjoint a.val b.val) (i j k l : Fin n)
    (ha : a.val = {i, j}) (hb : b.val = {k, l}) (hf : FourDistinct i j k l) :
    pairProjection (d := d) a b = projection (crossProposal i j k l hf) := by
  rw [pairProjection_of_disjoint a b h]
  obtain (⟨hi, hj⟩ | ⟨hi, hj⟩) := endpoints_cases a i j ha
  all_goals obtain (⟨hk, hl⟩ | ⟨hk, hl⟩) := endpoints_cases b k l hb
  all_goals simp only [pairProposal, hi, hj, hk, hl]
  · exact crossProjection_swap_right i j k l hf _
  · exact crossProjection_swap_left i j k l hf _
  · have hm : FourDistinct j i k l :=
      ⟨hf.1.symm, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.1, hf.2.2.1, hf.2.2.2.2.2⟩
    rw [crossProjection_swap_right j i k l hm, crossProjection_swap_left i j k l hf]

end Problem315.CrossToggle

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossToggleGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem gain_of_pairs (a b : Finset (Fin n)) (ha : a.card = 2) (hb : b.card = 2) :
    gain (d := d) a b = pairProjection ⟨a, ha⟩ ⟨b, hb⟩ := by
  simp [gain, ha, hb]

theorem gain_pair_eq (i j k l : Fin n) (h : FourDistinct i j k l) :
    gain (d := d) {i,j} {k,l} = SwitchFlip.projection (crossProposal i j k l h) := by
  have ha : ({i,j} : Finset (Fin n)).card = 2 := by simp [h.1]
  have hb : ({k,l} : Finset (Fin n)).card = 2 := by simp [h.2.2.2.2.2]
  have hd : Disjoint ({i,j} : Finset (Fin n)) {k,l} := by
    simp [Finset.disjoint_left, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  rw [gain_of_pairs _ _ ha hb]
  exact pairProjection_eq_explicit ⟨_,ha⟩ ⟨_,hb⟩ hd i j k l rfl rfl h

theorem gain_eq_zero_of_not_disjoint (a b : Finset (Fin n)) (h : ¬ Disjoint a b) :
    gain (d := d) a b = 0 := by
  by_cases ha : a.card = 2 <;> by_cases hb : b.card = 2 <;>
    simp [gain, ha, hb, pairProjection, h]

theorem gain_pair_eq_ordered (i j k l : Fin n) :
    gain (d := d) {i,j} {k,l} =
      if h : FourDistinct i k l j then
        SwitchFlip.projection (fourVertexProposal i k l j h) else 0 := by
  by_cases h : FourDistinct i k l j
  · rw [dite_eq_left h]
    have h' : FourDistinct i j k l :=
      ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.2.1.symm,
        h.2.2.2.2.2.symm, h.2.2.2.1⟩
    rw [gain_pair_eq i j k l h']
    rfl
  · rw [dite_eq_right h]
    by_cases hij : i = j
    · subst j
      simp [gain]
    by_cases hkl : k = l
    · subst l
      simp [gain]
    apply gain_eq_zero_of_not_disjoint
    intro hd
    apply h
    have hik : i ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hil : i ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show i ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjk : j ≠ k := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    have hjl : j ≠ l := by
      intro e
      exact Finset.disjoint_left.mp hd (show j ∈ ({i,j} : Finset (Fin n)) by simp)
        (by simp [← e])
    exact ⟨hik, hil, hij, hkl, hjk.symm, hjl.symm⟩

end Problem315.CrossToggle

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteKernelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteKernel

variable {α : Type*} [Fintype α]

theorem weighted_sq_sum_le
    (w f : α → ℝ)
    (hpos : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * f i ^ 2 := by
  let m := ∑ i, w i * f i
  have hvar : 0 ≤ ∑ i, w i * (f i - m) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i) (sq_nonneg _))
  have heq : (∑ i, w i * (f i - m) ^ 2) =
      (∑ i, w i * f i ^ 2) - m ^ 2 := by
    calc
      (∑ i, w i * (f i - m) ^ 2) =
          ∑ i, (w i * f i ^ 2 - 2 * m * (w i * f i) + w i * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * f i ^ 2) - m ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, hsum]
        change (∑ i, w i * f i ^ 2) - 2 * m * m + 1 * m ^ 2 = _
        ring
  rw [heq] at hvar
  dsimp [m] at hvar
  linarith

theorem sq_sum_apply_le
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, f i ^ 2 := by
  have hcol (j : α) : ∑ i, K i j = 1 := by
    simpa only [hsymm] using hrow j
  calc
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, ∑ j, K i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact weighted_sq_sum_le (K i) f (hpos i) (hrow i)
    _ = ∑ i, f i ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, hcol, one_mul]

theorem lazy_sq_sum_apply_le_inner
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤
      ∑ i, f i * (∑ j, K i j * f j) := by
  classical
  let Q (i j : α) : ℝ := 2 * K i j - if i = j then 1 else 0
  have hQrow (i : α) : ∑ j, Q i j = 1 := by
    norm_num [Q, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow]
  have hQsymm (i j : α) : Q i j = Q j i := by
    simp only [Q, hsymm i j, eq_comm]
  have hQpos (i j : α) : 0 ≤ Q i j := by
    by_cases hij : i = j
    · subst j
      simp only [Q, ite_true]
      linarith [hlazy i]
    · simp only [Q, hij, ite_false, sub_zero]
      exact mul_nonneg (by norm_num) (hpos i j)
  have hQapply (i : α) :
      (∑ j, Q i j * f j) = 2 * (∑ j, K i j * f j) - f i := by
    simp [Q, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hc := sq_sum_apply_le Q hQrow hQsymm hQpos f
  simp only [hQapply] at hc
  have hexpand : (∑ i, (2 * (∑ j, K i j * f j) - f i) ^ 2) =
      4 * (∑ i, (∑ j, K i j * f j) ^ 2) -
      4 * (∑ i, f i * (∑ j, K i j * f j)) + ∑ i, f i ^ 2 := by
    calc
      _ = ∑ i, (4 * (∑ j, K i j * f j) ^ 2 -
          4 * (f i * (∑ j, K i j * f j)) + f i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexpand] at hc
  linarith

theorem lazy_inner_nonneg
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    0 ≤ ∑ i, f i * (∑ j, K i j * f j) :=
  le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (lazy_sq_sum_apply_le_inner K hrow hsymm hpos hlazy f)

end Problem315.FiniteKernel

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SpectralFromSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem norm_apply_le_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hbound : ∀ x : E, ⟪x, T x⟫ ≤ r * ‖x‖ ^ 2)
    (x : E) : ‖T x‖ ≤ r * ‖x‖ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hev (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i ∧ ev i ≤ r := by
    constructor
    · simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
    · simpa only [hbe, inner_smul_right, hunit, mul_one, b.orthonormal.1 i,
        one_pow] using hbound (b i)
  have hsq : ‖T x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
      rw [← hT (b i) x, hbe, inner_smul_left]
      simp
    rw [hcoord, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hev i).1 (hev i).2 2
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hr (norm_nonneg x)]

omit [FiniteDimensional ℝ E] in

theorem norm_iterate_le
    (T : E →ₗ[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ x : E, ‖T x‖ ≤ r * ‖x‖) (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ r ^ t * ‖x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖T ((T : E → E)^[t] x)‖ ≤ r * ‖(T : E → E)^[t] x‖ := hbound _
        _ ≤ r * (r ^ t * ‖x‖) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (t + 1) * ‖x‖ := by ring

theorem norm_iterate_le_exp_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hgap : ∀ x : E, ⟪x, T x⟫ ≤ (1 - γ) * ‖x‖ ^ 2)
    (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
  have hr : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
  calc
    ‖(T : E → E)^[t] x‖ ≤ (1 - γ) ^ t * ‖x‖ :=
      norm_iterate_le T hr (norm_apply_le_of_inner_bounds T hT hr hpos hgap) t x
    _ ≤ (Real.exp (-γ)) ^ t * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg γ) t
    _ = Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteKernelTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace
open WithLp

namespace Problem315.Analytic

variable {α : Type*} [Fintype α]

lemma euclidean_inner_eq_sum (f g : EuclideanSpace ℝ α) :
    ⟪f, g⟫ = ∑ i, f i * g i := by
  simp [PiLp.inner_apply, mul_comm]

lemma euclidean_norm_sq_eq_sum (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ i, (f i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, euclidean_inner_eq_sum]
  simp [pow_two]

variable [DecidableEq α]

lemma matrix_preserves_zeroSum (K : Matrix α α ℝ)
    (hcols : ∀ j, ∑ i, K i j = 1) (f : EuclideanSpace ℝ α)
    (hf : f ∈ zeroSumSpace α) : Matrix.toEuclideanLin K f ∈ zeroSumSpace α := by
  change ∑ i, (Matrix.toEuclideanLin K f) i = 0
  simp only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcols, one_mul]
  exact hf

theorem matrix_centered_norm_decay (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hcols : ∀ j, ∑ i, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (f : EuclideanSpace ℝ α) (hf : ∑ i, f i = 0) :
    ‖(Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t] f‖ ≤
      Real.exp (-γ * (t : ℝ)) * ‖f‖ := by
  let T := Matrix.toEuclideanLin K
  have hinv := matrix_preserves_zeroSum K hcols
  let S := T.restrict hinv
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr hsymm)
  have hS : S.IsSymmetric := hT.restrict_invariant hinv
  have hSpos : ∀ x : zeroSumSpace α, 0 ≤ ⟪x, S x⟫ := by
    intro x
    change 0 ≤ ⟪(x : EuclideanSpace ℝ α), T x⟫
    simpa only [T, euclidean_inner_eq_sum, Matrix.toLpLin_apply, ofLp_toLp,
      Matrix.mulVec, dotProduct] using hpos (fun i => x.val i)
  have hSgap : ∀ x : zeroSumSpace α, ⟪x, S x⟫ ≤ (1 - γ) * ‖x‖ ^ 2 := by
    intro x
    change ⟪(x : EuclideanSpace ℝ α), T x⟫ ≤ (1 - γ) * ‖(x : EuclideanSpace ℝ α)‖ ^ 2
    rw [euclidean_inner_eq_sum, euclidean_norm_sq_eq_sum]
    simp only [T, Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
    have hh := hgap (fun i => x.val i) x.property
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← pow_two] at hh
    linarith
  have hdec := norm_iterate_le_exp_of_inner_bounds S hS hγ hSpos hSgap t ⟨f, hf⟩
  have hiter (k : ℕ) :
      ((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val =
        (T : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[k] f := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        change T (((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val) = _
        rw [ih]
  change ‖(((S : zeroSumSpace α → zeroSumSpace α)^[t] ⟨f, hf⟩).val)‖ ≤
    Real.exp (-γ * (t : ℝ)) * ‖f‖ at hdec
  rwa [hiter] at hdec

omit [DecidableEq α] in
lemma sum_abs_le_sqrt_card_mul_norm (f : EuclideanSpace ℝ α) :
    (∑ i, |f i|) ≤ Real.sqrt (Fintype.card α : ℝ) * ‖f‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : α => (1 : ℝ)) (fun i => |f i|)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs, ← euclidean_norm_sq_eq_sum, Real.sqrt_sq (norm_nonneg f)] using h

lemma centeredPoint_sum (a : α) : ∑ i, centeredPoint a i = 0 := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centeredPoint, Finset.sum_sub_distrib, hn]

lemma centeredPoint_norm_sq (a : α) :
    ‖centeredPoint a‖ ^ 2 = 1 - 1 / (Fintype.card α : ℝ) := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [euclidean_norm_sq_eq_sum]
  simp only [centeredPoint, ofLp_toLp, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [ite_pow, one_pow, zero_pow (by omega : (2 : ℕ) ≠ 0), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma centeredPoint_norm_le_one (a : α) : ‖centeredPoint a‖ ≤ 1 := by
  have h := centeredPoint_norm_sq a
  have hn : 0 ≤ 1 / (Fintype.card α : ℝ) := by positivity
  nlinarith [norm_nonneg (centeredPoint a)]

lemma matrix_pow_row_sum (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) : ∀ i, ∑ j, (K ^ t) i j = 1 := by
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
      intro i
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrows, mul_one]
      exact ih i

lemma matrix_iterate_centeredPoint (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) (a i : α) :
    ((Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
      (centeredPoint a)) i = (K ^ t) i a - 1 / (Fintype.card α : ℝ) := by
  rw [← Module.End.pow_apply]
  change ((Matrix.toLpLin 2 2 K ^ t) (centeredPoint a)) i = _
  rw [← Matrix.toLpLin_pow, Matrix.toLpLin_apply]
  simp only [ofLp_toLp, Matrix.mulVec, dotProduct, centeredPoint, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, matrix_pow_row_sum K hrows t,
    one_mul]
  simp

theorem matrix_tv_bound_of_gap (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hrows : ∀ i, ∑ j, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (a : α) :
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  have hcols : ∀ j, ∑ i, K i j = 1 := by
    intro j
    calc
      ∑ i, K i j = ∑ i, K j i := Finset.sum_congr rfl (fun i _ => hsymm.apply j i)
      _ = 1 := hrows j
  let f := (Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
    (centeredPoint a)
  have heq (i : α) : f i = (K ^ t) a i - 1 / (Fintype.card α : ℝ) := by
    dsimp only [f]
    rw [matrix_iterate_centeredPoint K hrows, (hsymm.pow t).apply a i]
  have hnorm : ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) := by
    calc
      ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖centeredPoint a‖ :=
        matrix_centered_norm_decay K hsymm hcols hγ hpos hgap t
          (centeredPoint a) (centeredPoint_sum a)
      _ ≤ Real.exp (-γ * (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (centeredPoint_norm_le_one a) (Real.exp_nonneg _)
      _ = _ := mul_one _
  calc
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) =
        (1 / 2 : ℝ) * ∑ i, |f i| := by simp_rw [heq]
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul_norm f) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) *
        Real.exp (-γ * (t : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = _ := by ring

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.InitialTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315Aux

theorem deltaUniformTV_eq {α : Type*} [Fintype α] (x : α) :
    deltaUniformTV x = 1 - 1 / (Fintype.card α : ℝ) := by
  classical
  have : Nonempty α := ⟨x⟩
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc1 : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (Fintype.card_pos (α := α))
  have hi : (1 : ℝ) / Fintype.card α ≤ 1 := (div_le_one hc).2 hc1
  have hi0 : (0 : ℝ) ≤ 1 / Fintype.card α := le_of_lt (one_div_pos.mpr hc)
  have habs (y : α) :
      |(if x = y then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)| =
      (if x = y then 1 - 2 / (Fintype.card α : ℝ) else 0) +
        1 / (Fintype.card α : ℝ) := by
    by_cases hxy : x = y
    · simp only [hxy, ite_true, abs_of_nonneg (sub_nonneg.mpr hi)]
      ring
    · simp only [hxy, ite_false, zero_sub, abs_neg, abs_of_nonneg hi0, zero_add]
  unfold deltaUniformTV
  simp_rw [habs]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp [ne_of_gt hc]
  ring

end Problem315Aux

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.InitialTVGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

theorem tvDistanceFrom_zero_eq (n : Nat) (d : Fin n → Nat) (G : GraphState n d) :
    tvDistanceFrom n d 0 G = 1 - 1 / (stateCount n d : ℝ) := by
  classical
  have hid : tvDistanceFrom n d 0 G = Problem315Aux.deltaUniformTV G := by
    simp only [tvDistanceFrom, kernelPow, stateCount, allGraphStates,
      Problem315Aux.deltaUniformTV, Finset.card_univ]
    congr 1
    apply Finset.sum_congr rfl
    intro H _
    by_cases heq : G = H <;> simp [heq]
  rw [hid, Problem315Aux.deltaUniformTV_eq]
  rfl

theorem mixedAt_zero_of_stateCount_one (n : Nat) (d : Fin n → Nat)
    (hc : stateCount n d = 1) : MixedAt n d 0 := by
  intro G
  rw [tvDistanceFrom_zero_eq, hc]
  norm_num

theorem mixingTime_zero_of_mixedAt_zero (n : Nat) (d : Fin n → Nat)
    (hzero : MixedAt n d 0) (h : ∃ t : Nat, MixedAt n d t) :
    mixingTime n d h = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h hzero)

theorem singleton_mixing_conclusion (n : Nat) (d : Fin n → Nat)
    (hc : stateCount n d = 1) :
    MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0 := by
  have hzero := mixedAt_zero_of_stateCount_one n d hc
  exact ⟨hzero, mixingTime_zero_of_mixedAt_zero n d hzero⟩

theorem mixedAt_zero_iff_stateCount_le_one (n : Nat) (d : Fin n → Nat) :
    MixedAt n d 0 ↔ stateCount n d ≤ 1 := by
  classical
  constructor
  · intro hm
    by_contra hc
    have htwo : 2 ≤ stateCount n d := by omega
    have hpos : 0 < (allGraphStates n d).card := by
      change 0 < stateCount n d
      omega
    obtain ⟨G, _⟩ := Finset.card_pos.mp hpos
    have htwoR : (2 : ℝ) ≤ stateCount n d := by exact_mod_cast htwo
    have hinv : (1 : ℝ) / stateCount n d ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) htwoR
    have hG := hm G
    rw [tvDistanceFrom_zero_eq] at hG
    linarith
  · intro hc G
    have : Nonempty (GraphState n d) := ⟨G⟩
    have hpos : 0 < stateCount n d := by
      simpa [stateCount, allGraphStates] using
        (Fintype.card_pos (α := GraphState n d))
    have hone : stateCount n d = 1 := by omega
    exact mixedAt_zero_of_stateCount_one n d hone G

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

theorem assignment_natCard (G : SimpleGraph V) (i j : V) :
    Nat.card (Assignment G i j) =
      Nat.choose (singletonSet G i j).card (leftSet G i j).card := by
  classical
  let e : Assignment G i j ≃ ((singletonSet G i j).powersetCard (leftSet G i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : Nat}

theorem fiberStates_card {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G).card =
      Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
  classical
  calc
    _ = Nat.card (PairResampling.fiberStates {i, j} G) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (Assignment G.val i j) := Nat.card_congr (resamplingFiberEquiv G i j hij)
    _ = _ := assignment_natCard G.val i j

theorem expectation_eq_assignment_average {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : PairResampling.StateSpace n d) :
    PairResampling.expectation n d {i, j} f G =
      (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) := by
  classical
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
    (fun H : (PairResampling.fiberStates {i, j} G) => f H.val)).symm

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberSliceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

open SlicePermutationAction
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem assignmentRelabel_swap_val (G : SimpleGraph V) (i j : V)
    (x y : singletonSet G i j) (T : Assignment G i j) :
    (assignmentRelabel G i j (Equiv.swap x y) T).val =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
  classical
  change ((T.val.subtype (fun z => z ∈ singletonSet G i j)).map
    (Equiv.swap x y).toEmbedding).map
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) = _
  rw [Finset.map_map]
  have he : (Equiv.swap x y).toEmbedding.trans
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)) =
      (Function.Embedding.subtype (fun z => z ∈ singletonSet G i j)).trans
        (Equiv.swap x.val y.val).toEmbedding := by
    ext z
    exact Function.Injective.map_swap Subtype.val_injective x y z
  rw [he, ← Finset.map_map, Finset.subtype_map_of_mem T.property.1]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairTradeSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairFiber

theorem fourVertexState_key {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    key i j (fourVertexState G i u v j h).val = key i j G.val := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  apply key_eq_of
  · intro x y hx hy
    change (proposalResult G.val (fourVertexProposal i u v j h)).Adj x y ↔ _
    rw [proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj]
    simp [hx.1, hx.2, hy.1, hy.2]
  · rw [hl]
    simp [h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]
  · intro w
    have hju : ¬ G.val.Adj j u := fun hadj => huj hadj.symm
    have hjv : G.val.Adj j v := hvj.symm
    by_cases hwu : w = u
    · subst w
      simp [edgeBit, hl, hr, hiu, hju, h.2.2.2.1]
    by_cases hwv : w = v
    · subst w
      simp [edgeBit, hl, hr, hiv, hjv, h.2.2.2.1.symm]
    simp [edgeBit, hl, hr, hwu, hwv]

theorem fourVertexState_leftSet {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hiu : G.val.Adj i u) (hvj : G.val.Adj v j)
    (hiv : ¬ G.val.Adj i v) (huj : ¬ G.val.Adj u j) :
    leftSet (fourVertexState G i u v j h).val i j =
      insert v ((leftSet G.val i j).erase u) := by
  classical
  have hl (w : Fin n) : (fourVertexState G i u v j h).val.Adj i w ↔
      (G.val.Adj i w ∧ w ≠ u) ∨ w = v :=
    proposalResult_fourVertex_adj_first G.val i u v j h hiu hvj hiv huj w
  have hr (w : Fin n) : (fourVertexState G i u v j h).val.Adj j w ↔
      (G.val.Adj j w ∧ w ≠ v) ∨ w = u := by
    simpa [fourVertexState, h.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm] using
      proposalResult_fourVertex_adj G.val i u v j h hiu hvj hiv huj j w
  ext w
  simp only [mem_leftSet, Finset.mem_insert, Finset.mem_erase, hl, hr]
  by_cases hwu : w = u
  · subst w
    simp [h.2.2.2.1]
  by_cases hwv : w = v
  · subst w
    simp [Outside, h.2.1.symm, h.2.2.2.2.2, h.2.2.2.1.symm]
  simp [hwu, hwv, and_comm]

theorem map_swap_eq_exchange {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hu : u ∈ A) (hv : v ∉ A) :
    A.map (Equiv.swap u v).toEmbedding = insert v (A.erase u) := by
  classical
  have huv : u ≠ v := fun heq => hv (heq ▸ hu)
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hwu : w = u
  · subst w
    simp [huv, hv]
  by_cases hwv : w = v
  · subst w
    simp [hu]
  simp [Equiv.swap_apply_of_ne_of_ne hwu hwv, hwu, hwv]

theorem map_swap_eq_self_of_mem_iff {V : Type*} [DecidableEq V]
    (A : Finset V) (u v : V) (hmem : u ∈ A ↔ v ∈ A) :
    A.map (Equiv.swap u v).toEmbedding = A := by
  classical
  ext w
  simp only [Finset.mem_map_equiv, Equiv.symm_swap]
  by_cases hwu : w = u
  · subst w
    simpa using hmem.symm
  by_cases hwv : w = v
  · subst w
    simpa using hmem
  rw [Equiv.swap_apply_of_ne_of_ne hwu hwv]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling

variable {n : Nat} {d : Fin n → Nat}

theorem sum_expectation (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ G, expectation n d a f G) = ∑ G, f G := by
  let one : StateSpace n d := WithLp.toLp 2 (fun _ => 1)
  have hone : expectation n d a one = one :=
    (expectation_eq_self_iff a one).mpr (constant_mem a 1)
  have h := expectation_isSymmetric a f one
  change inner ℝ (expectation n d a f) one = inner ℝ f (expectation n d a one) at h
  rw [hone, state_inner, state_inner] at h
  simpa [one] using h

theorem sum_fiber_average (a : Finset (Fin n)) (g : GraphState n d → ℝ) :
    (∑ G, (∑ H ∈ fiberStates a G, g H) / (fiberStates a G).card) = ∑ G, g G := by
  let f : StateSpace n d := WithLp.toLp 2 g
  have h := sum_expectation a f
  simpa only [expectation_eq_average, f] using h

end Problem315.PairResampling

namespace Problem315.PairFiber

variable {n : Nat} {d : Fin n → Nat}

theorem assignment_average_eq_fiber_average
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (g : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, g ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      (∑ H ∈ PairResampling.fiberStates {i, j} G, g H) /
        (PairResampling.fiberStates {i, j} G).card := by
  let f : PairResampling.StateSpace n d := WithLp.toLp 2 g
  have h := expectation_eq_assignment_average G i j hij f
  rw [PairResampling.expectation_eq_average] at h
  exact h.symm

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MixingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

theorem switch_denominator_le_pow_six (n : ℕ) :
    24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 6 := by
  have h := Nat.choose_le_pow_div (α := ℝ) 4 n
  norm_num at h
  nlinarith [sq_nonneg (n : ℝ)]

theorem exponential_tv_bound_at_polynomial_time (n s : ℕ)
    (hn : 4 ≤ n) (hs : s ≤ 2 ^ (n * n)) :
    Real.sqrt (s : ℝ) / 2 *
      Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) ≤ (1 : ℝ) / 4 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hchoose : 0 < (n.choose 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hdenom : 0 < 24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ) := by positivity
  have hratio : 2 * (n : ℝ) ^ 2 ≤
      ((2 * n ^ 8 : ℕ) : ℝ) / (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)) := by
    apply (le_div_iff₀ hdenom).2
    calc
      2 * (n : ℝ) ^ 2 * (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))
          ≤ 2 * (n : ℝ) ^ 2 * (n : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_left (switch_denominator_le_pow_six n) (by positivity)
      _ = ((2 * n ^ 8 : ℕ) : ℝ) := by push_cast; ring
  have hsqrt : Real.sqrt (s : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
    have hsqrt' : Real.sqrt (s : ℝ) ≤ (s : ℝ) := by
      apply Real.sqrt_le_self_iff.mpr
      rcases Nat.eq_zero_or_pos s with h | h
      · left; simp [h]
      · right; exact_mod_cast h
    calc
      Real.sqrt (s : ℝ) ≤ (s : ℝ) := hsqrt'
      _ ≤ (2 : ℝ) ^ (n * n) := by exact_mod_cast hs
      _ ≤ Real.exp 1 ^ (n * n) :=
        pow_le_pow_left₀ (by norm_num) (by have := Real.add_one_le_exp (1 : ℝ); linarith) _
      _ = Real.exp ((n : ℝ) ^ 2) := by rw [Real.exp_one_pow]; congr 1; push_cast; ring
  have hexp : Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
      (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ))) ≤ Real.exp (-2 * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hsmall : Real.exp (-((n : ℝ) ^ 2)) ≤ (1 : ℝ) / 2 := by
    have hlarge : (2 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by
      have := Real.add_one_le_exp ((n : ℝ) ^ 2)
      nlinarith
    simpa [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlarge
  calc
    Real.sqrt (s : ℝ) / 2 * Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
        (24 * (n : ℝ) ^ 2 * (n.choose 4 : ℝ)))
        ≤ Real.exp ((n : ℝ) ^ 2) / 2 * Real.exp (-2 * (n : ℝ) ^ 2) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hsqrt (by norm_num)) hexp
        (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (-((n : ℝ) ^ 2)) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 : ℝ) / 4 := by linarith

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MixingTimeFromTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315

theorem stateCount_le_two_pow_square (n : ℕ) (d : Fin n → ℕ) :
    stateCount n d ≤ 2 ^ (n ^ 2) := by
  classical
  have hinj : Function.Injective (fun G : GraphState n d => G.val.Adj) := by
    intro G H h
    apply Subtype.ext
    apply SimpleGraph.ext
    exact h
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa [stateCount, allGraphStates, Fintype.card_fun, pow_mul, pow_two] using hcard

theorem mixedAt_polynomial_of_tv_estimate (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hTV : ∀ G : GraphState n d,
      tvDistanceFrom n d (2 * n ^ 8) G ≤
        Real.sqrt (stateCount n d : ℝ) / 2 *
          Real.exp (- ((2 * n ^ 8 : ℕ) : ℝ) /
            (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    MixedAt n d (2 * n ^ 8) := by
  classical
  intro G
  exact (hTV G).trans (exponential_tv_bound_at_polynomial_time n
    (stateCount n d) hn (by simpa [pow_two] using stateCount_le_two_pow_square n d))

theorem exists_mixingTime_le_of_mixedAt (n : ℕ) (d : Fin n → ℕ) (t : ℕ)
    (ht : MixedAt n d t) :
    ∃ h : (∃ s : ℕ, MixedAt n d s), mixingTime n d h ≤ t := by
  classical
  refine ⟨⟨t, ht⟩, ?_⟩
  exact Nat.find_min' _ ht

theorem polynomial_mixing_of_tv_bound (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hTV : ∀ (t : ℕ) (G : GraphState n d),
      tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
        Real.exp (- (t : ℝ) /
          (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    ∃ h : (∃ t : ℕ, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8 := by
  exact exists_mixingTime_le_of_mixedAt n d (2 * n ^ 8)
    (mixedAt_polynomial_of_tv_estimate n d hn (hTV (2 * n ^ 8)))

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem315

lemma kernelPow_eq_matrix_pow (n : ℕ) (d : Fin n → ℕ) (t : ℕ) :
    (kernelPow n d t : Matrix (GraphState n d) (GraphState n d) ℝ) =
      (Matrix.of (switchKernel n d)) ^ t := by
  classical
  induction t with
  | zero =>
      funext G H
      change (if G = H then (1 : ℝ) else 0) = (1 : Matrix (GraphState n d) (GraphState n d) ℝ) G H
      simp [Matrix.one_apply]
  | succ t ih =>
      funext G H
      change (∑ K ∈ allGraphStates n d, kernelPow n d t G K * switchKernel n d K H) = _
      rw [ih, pow_succ]
      rfl

theorem switch_tv_bound_of_gap (n : ℕ) (d : Fin n → ℕ)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    {γ : ℝ} (hγ : γ ≤ 1) (hgap : hasSpectralGapAtLeast n d γ)
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤
      Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  classical
  have : Nonempty (GraphState n d) := ⟨G⟩
  have hN : (0 : ℝ) < (Fintype.card (GraphState n d) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsymm : Matrix.IsSymm (Matrix.of (switchKernel n d)) :=
    Matrix.IsSymm.ext (fun G H => switchKernel_symm H G)
  have hpos : ∀ f : GraphState n d → ℝ,
      0 ≤ ∑ G, f G * ∑ H, switchKernel n d G H * f H :=
    FiniteKernel.lazy_inner_nonneg (switchKernel n d) hrows switchKernel_symm
      switchKernel_nonneg switchKernel_self_ge_half
  have hgap' : ∀ f : GraphState n d → ℝ, (∑ G, f G) = 0 →
      γ * (∑ G, (f G) ^ 2) ≤
        ∑ G, f G * (f G - ∑ H, switchKernel n d G H * f H) := by
    intro f hf
    have hh := hgap f
    have havg : uniformAverage n d f = 0 := by
      simp [uniformAverage, allGraphStates, hf]
    unfold uniformVariance at hh
    rw [havg] at hh
    simp only [sub_zero, uniformAverage, stateCount,
      allGraphStates, Finset.card_univ, dirichletEnergy, uniformInner, markovApply] at hh
    rw [← mul_div_assoc] at hh
    exact (div_le_div_iff_of_pos_right hN).mp hh
  have ht := Analytic.matrix_tv_bound_of_gap (Matrix.of (switchKernel n d)) hsymm hrows hγ hpos hgap' t G
  simpa only [tvDistanceFrom, allGraphStates, stateCount, Finset.card_univ,
    kernelPow_eq_matrix_pow] using ht

lemma switch_gap_parameter_le_one (n : ℕ) (hn : 4 ≤ n) :
    (1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) ≤ 1 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose n 4 : ℝ) := by
    exact_mod_cast (Nat.choose_pos hn)
  have hd : (1 : ℝ) ≤ 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hn')) hc
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd

theorem switch_chain_tv_bound_of_stochastic_and_gap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  have h := switch_tv_bound_of_gap n d hrows (switch_gap_parameter_le_one n hn) hgap t G
  convert h using 1
  congr 2
  ring

theorem switch_chain_tv_bound_of_spectralGap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  apply switch_chain_tv_bound_of_stochastic_and_gap n d hn _ hgap t G
  intro H
  simpa only [allGraphStates] using switchKernel_row_sum hn H

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MainFromGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315

theorem switch_chain_main_of_spectralGap (n : Nat) (d : Fin n → Nat)
    (hn : 4 ≤ n)
    (hgap : 1 < stateCount n d → hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) :
    (∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧
      (stateCount n d = 1 →
        MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0) ∧
      (1 < stateCount n d → hasSpectralGapAtLeast n d
        ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)))) := by
  refine ⟨?_, singleton_mixing_conclusion n d, hgap⟩
  by_cases hlarge : 1 < stateCount n d
  · exact polynomial_mixing_of_tv_bound n d hn
      (switch_chain_tv_bound_of_spectralGap n d hn (hgap hlarge))
  · have hzero : MixedAt n d 0 :=
      (mixedAt_zero_iff_stateCount_le_one n d).mpr (by omega)
    obtain ⟨h, hh⟩ := exists_mixingTime_le_of_mixedAt n d 0 hzero
    exact ⟨h, hh.trans (Nat.zero_le _)⟩

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem active_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    active i j k l G ↔ active i j k l H := by
  have hh := singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G.val H.val).mp h)
  unfold active
  rw [hh]

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProjectionTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem315
namespace ProjectionTools

open scoped BigOperators

theorem sum_disjoint_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset (ι × ι)) (cross gain err : ι → ι → ℝ)
    (hsymm : ∀ p ∈ s, p.swap ∈ s)
    (hlocal : ∀ a b, (a,b) ∈ s →
      2 * gain a b - err a b - err b a ≤ 2 * cross a b)
    (hbudget : (∑ p ∈ s, err p.1 p.2) ≤ ∑ p ∈ s, gain p.1 p.2) :
    0 ≤ ∑ p ∈ s, cross p.1 p.2 := by
  have hswap : (∑ p ∈ s, err p.2 p.1) = ∑ p ∈ s, err p.1 p.2 := by
    apply Finset.sum_bij (fun p _ => p.swap)
    · intro p hp
      exact hsymm p hp
    · intro p hp q hq hpq
      exact Prod.swap_injective hpq
    · intro p hp
      exact ⟨p.swap, hsymm p hp, Prod.swap_swap p⟩
    · intro p hp
      rfl
  have hsum := Finset.sum_le_sum (s := s) (fun p hp => hlocal p.1 p.2 hp)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  linarith

open scoped RealInnerProductSpace

end ProjectionTools
end Problem315

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairDisjointBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem disjoint_sum_nonneg_of_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d → StateSpace n d)
    (hlocal : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b f‖ ^ 2 - ‖R a b f‖ ^ 2 - ‖R b a f‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b f‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b f‖ ^ 2 else 0) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  classical
  let s := (pairs n ×ˢ pairs n).filter (fun p => Disjoint p.1 p.2)
  have hmem (a b : Finset (Fin n)) :
      (a,b) ∈ s ↔ a ∈ pairs n ∧ b ∈ pairs n ∧ Disjoint a b := by
    simp only [s, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum (F : Finset (Fin n) → Finset (Fin n) → ℝ) :
      (∑ p ∈ s, F p.1 p.2) =
        ∑ a ∈ pairs n, ∑ b ∈ pairs n, if Disjoint a b then F a b else 0 := by
    rw [show s = (pairs n ×ˢ pairs n).filter
      (fun p => Disjoint p.1 p.2) from rfl, Finset.sum_filter, Finset.sum_product]
  have h := ProjectionTools.sum_disjoint_nonneg s
    (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (fun a b => ‖g a b f‖ ^ 2) (fun a b => ‖R a b f‖ ^ 2) ?_ ?_ ?_
  · rw [hsum (fun a b => ⟪fluctuation n d a f, fluctuation n d b f⟫)] at h
    exact h
  · rintro ⟨a,b⟩ hab
    have hp := (hmem a b).mp hab
    exact (hmem b a).mpr ⟨hp.2.1, hp.1, hp.2.2.symm⟩
  · intro a b hab
    have hp := (hmem a b).mp hab
    exact hlocal a hp.1 b hp.2.1 hp.2.2
  · rw [hsum (fun a b => ‖R a b f‖ ^ 2), hsum (fun a b => ‖g a b f‖ ^ 2)]
    exact Finset.sum_le_sum hbudget

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem singleton_adj_equal_swap (G : SimpleGraph V) (i j k l : V)
    (hk : k ∈ singletonSet G i j) (hl : l ∈ singletonSet G i j) :
    (G.Adj i k ↔ G.Adj i l) ↔ (G.Adj j k ↔ G.Adj j l) := by
  have hk' := (mem_singletonSet G i j k).mp hk
  have hl' := (mem_singletonSet G i j l).mp hl
  simp only [Xor] at hk' hl'
  tauto

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem observable_eq_of_active (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) : observable i k l G = observable j k l G := by
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1 : ℝ) else 0) =
    if G.val.Adj j k ↔ G.val.Adj j l then 1 else 0
  simp only [singleton_adj_equal_swap G.val i j k l ha.1 ha.2]

theorem centered_eq_of_active (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (ha : active i j k l G) :
    centered i j k l G = centered j i k l G := by
  unfold centered
  rw [fluctuation_eq_sub, fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G =
    observable j k l G - expectation n d {j,i} (observable j k l) G
  rw [observable_eq_of_active i j k l G ha, Finset.pair_comm j i]
  congr 1
  rw [expectation_eq_average, expectation_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro H hH
  exact observable_eq_of_active i j k l H
    ((active_sameFiber i j k l hij ((mem_fiberStates {i,j} G H).mp hH)).mp ha)

theorem gated_centered_swap_left (i j k l : Fin n) (hij : i ≠ j)
    (G H : GraphState n d) (h : SameFiber {i,j} G.val H.val) :
    (if active i j k l G then centered i j k l H else 0) =
      (if active j i k l G then centered j i k l H else 0) := by
  simp only [active_swap_left]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
    exact centered_eq_of_active i j k l hij H ((active_sameFiber i j k l hij h).mp ha)
  · simp only [ite_eq_right ha]

theorem equalitySpace_le_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l ≤ equalitySpace j i k l := by
  intro f hf G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, fun H h => ?_⟩
  have h' : SameFiber {i,j} G.val H.val := by
    simpa only [Finset.pair_comm j i] using h
  rw [hc H h', gated_centered_swap_left i j k l hij G H h']

theorem equalitySpace_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l = equalitySpace j i k l :=
  le_antisymm (equalitySpace_le_swap_left i j k l hij)
    (equalitySpace_le_swap_left j i k l hij.symm)

theorem equalitySpace_swap_right (i j k l : Fin n) :
    equalitySpace (d := d) i j k l = equalitySpace i j l k := by
  ext f
  simp only [equalitySpace, Submodule.mem_mk,
    active_swap_right, centered_swap_right]

theorem projection_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    projection (d := d) i j k l = projection j i k l := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_left i j k l hij)

theorem projection_swap_right (i j k l : Fin n) :
    projection (d := d) i j k l = projection i j l k := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_right i j k l)

theorem projection_eq_of_left_pair_eq (i j i' j' k l : Fin n) (hij : i ≠ j)
    (h : ({i,j} : Finset (Fin n)) = {i',j'}) :
    projection (d := d) i j k l = projection i' j' k l := by
  have hs : ({i,j} : Set (Fin n)) = {i',j'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_left _ _ _ _ hij

theorem projection_eq_of_right_pair_eq (i j k l k' l' : Fin n)
    (h : ({k,l} : Finset (Fin n)) = {k',l'}) :
    projection (d := d) i j k l = projection i j k' l' := by
  have hs : ({k,l} : Set (Fin n)) = {k',l'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_right _ _ _ _

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityUnordered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem equalitySpace_eq_bot_of_inactive (i j k l : Fin n)
    (h : ∀ G : GraphState n d, ¬ active i j k l G) :
    equalitySpace (d := d) i j k l = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    ext G
    change f G = 0
    obtain ⟨c, hc⟩ := hf G
    have he := hc G (SameFiber.refl _ _)
    simpa only [ite_eq_right (h G), mul_zero] using he
  · exact bot_le

theorem projection_eq_zero_of_not_disjoint (i j k l : Fin n)
    (h : ¬ Disjoint ({i,j} : Finset (Fin n)) {k,l}) :
    projection (d := d) i j k l = 0 := by
  have hinactive : ∀ G : GraphState n d, ¬ active i j k l G := by
    intro G ha
    obtain ⟨v,hv,hv'⟩ := Finset.not_disjoint_iff.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    have hk := ((mem_singletonSet G.val i j k).mp ha.1).1
    have hl := ((mem_singletonSet G.val i j l).mp ha.2).1
    rcases hv with rfl | rfl <;> rcases hv' with hv' | hv'
    · exact hk.1 hv'.symm
    · exact hl.1 hv'.symm
    · exact hk.2 hv'.symm
    · exact hl.2 hv'.symm
  have he := congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_eq_bot_of_inactive i j k l hinactive)
  exact he.trans Submodule.starProjection_bot

private theorem endpoints_spec (a : Finset (Fin n)) (ha : a.card = 2) :
    (endpoints a ha).1 ≠ (endpoints a ha).2 ∧
      a = {(endpoints a ha).1,(endpoints a ha).2} :=
  Classical.choose_spec (exists_pair_endpoints a ha)

theorem pairProjection_eq (a b : Finset (Fin n))
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : a = {i,j}) (hb : b = {k,l}) :
    pairProjection (d := d) a b = projection i j k l := by
  have hca : a.card = 2 := by rw [ha]; simp [hij]
  have hcb : b.card = 2 := by rw [hb]; simp [hkl]
  rw [pairProjection, dite_eq_left hca, dite_eq_left hcb]
  have hpa := endpoints_spec a hca
  have hpb := endpoints_spec b hcb
  calc
    _ = projection i j (endpoints b hcb).1 (endpoints b hcb).2 :=
      projection_eq_of_left_pair_eq _ _ _ _ _ _ hpa.1 (hpa.2.symm.trans ha)
    _ = _ := projection_eq_of_right_pair_eq _ _ _ _ _ _ (hpb.2.symm.trans hb)

@[simp] theorem pairProjection_pair (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    pairProjection (d := d) {i,j} {k,l} = projection i j k l :=
  pairProjection_eq _ _ i j k l hij hkl rfl rfl

@[simp] theorem pairProjection_eq_zero_left (a b : Finset (Fin n))
    (ha : a.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  simp only [pairProjection, dite_eq_right ha]

theorem pairProjection_eq_zero_of_not_disjoint (a b : Finset (Fin n))
    (hab : ¬ Disjoint a b) : pairProjection (d := d) a b = 0 := by
  by_cases ha : a.card = 2
  · by_cases hb : b.card = 2
    · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
      obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp hb
      rw [pairProjection_pair i j k l hij hkl]
      exact projection_eq_zero_of_not_disjoint i j k l hab
    · exact pairProjection_eq_zero_right a b hb
  · exact pairProjection_eq_zero_left a b ha

theorem sum_pairProjection_norm_sq (a : Finset (Fin n))
    (s : Finset (Finset (Fin n))) (f : StateSpace n d) :
    (∑ b ∈ s, if Disjoint a b then ‖pairProjection a b f‖ ^ 2 else 0) =
      ∑ b ∈ s, ‖pairProjection a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, pairProjection_eq_zero_of_not_disjoint a b hab]
    simp

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairDisjointAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem interaction_on_pairs_of_named {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (a : Finset (Fin n)) (ha : a ∈ pairs n)
    (b : Finset (Fin n)) (hb : b ∈ pairs n) (hab : Disjoint a b) :
    2 * ‖CrossToggle.gain a b f‖ ^ 2 - ‖PairEquality.pairProjection a b f‖ ^ 2 -
      ‖PairEquality.pairProjection b a f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hca : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  have hcb : b.card = 2 := (Finset.mem_powersetCard.mp hb).2
  let A : CrossToggle.VertexPair n := ⟨a, hca⟩
  let B : CrossToggle.VertexPair n := ⟨b, hcb⟩
  have hA : a = {CrossToggle.first A, CrossToggle.second A} := CrossToggle.pair_eq A
  have hB : b = {CrossToggle.first B, CrossToggle.second B} := CrossToggle.pair_eq B
  have hfour := CrossToggle.endpoints_distinct A B hab
  have hg : CrossToggle.gain (d := d) a b =
      SwitchFlip.projection (CrossToggle.crossProposal
        (CrossToggle.first A) (CrossToggle.second A)
        (CrossToggle.first B) (CrossToggle.second B) hfour) := by
    rw [CrossToggle.gain_of_pairs a b hca hcb]
    exact CrossToggle.pairProjection_of_disjoint A B hab
  rw [hg,
    PairEquality.pairProjection_eq a b _ _ _ _
      (CrossToggle.first_ne_second A) (CrossToggle.first_ne_second B) hA hB,
    PairEquality.pairProjection_eq b a _ _ _ _
      (CrossToggle.first_ne_second B) (CrossToggle.first_ne_second A) hB hA]
  simpa only [← hA, ← hB] using hlocal _ _ _ _ hfour

theorem disjoint_sum_nonneg_of_named_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, ‖PairEquality.pairProjection a b f‖ ^ 2) ≤
        ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  apply disjoint_sum_nonneg_of_interaction_budget f
    (fun a b => CrossToggle.gain a b) (fun a b => PairEquality.pairProjection a b)
    (interaction_on_pairs_of_named f hlocal)
  intro a ha
  rw [PairEquality.sum_pairProjection_norm_sq]
  have hg : (∑ b ∈ pairs n, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0) =
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : Disjoint a b
    · rw [ite_eq_left hab]
    · rw [ite_eq_right hab, CrossToggle.gain_eq_zero_of_not_disjoint a b hab]
      simp
  rw [hg]
  exact hbudget a ha

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem gatedCentered_mem (i j k l : Fin n) (hij : i ≠ j) :
    gatedCentered (d := d) i j k l ∈ equalitySpace i j k l := by
  intro G
  refine ⟨1, fun H h => ?_⟩
  have ha := active_sameFiber i j k l hij h
  change (if active i j k l H then _ else 0) = _
  simp only [one_mul, ha]

theorem restrictCell_mem (i j k l : Fin n)
    (C : GraphState n d → Prop) (hC : CellInvariant {i,j} C)
    (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    restrictCell C f ∈ equalitySpace i j k l := by
  intro G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨if C G then c else 0, fun H h => ?_⟩
  rw [restrictCell_apply, ← hC G H h]
  by_cases hG : C G
  · simpa only [ite_eq_left hG] using hc H h
  · simp only [ite_eq_right hG, zero_mul]

theorem fiberCell_invariant (a : Finset (Fin n)) (G : GraphState n d) :
    CellInvariant a (fun H : GraphState n d => SameFiber a G.val H.val) := by
  intro H K h
  exact ⟨fun hG => hG.trans h, fun hG => hG.trans h.symm⟩

theorem localizedVector_mem (i j k l : Fin n) (hij : i ≠ j) (G : GraphState n d) :
    localizedVector i j k l G ∈ equalitySpace i j k l :=
  restrictCell_mem i j k l _ (fiberCell_invariant _ G) _
    (gatedCentered_mem i j k l hij)

theorem restrict_eq_smul_localizedVector (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) (hf : f ∈ equalitySpace i j k l) :
    ∃ c : ℝ, restrictCell (fun H => SameFiber {i,j} G.val H.val) f =
      c • localizedVector i j k l G := by
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, ?_⟩
  ext H
  by_cases h : SameFiber {i,j} G.val H.val
  · change (if SameFiber {i,j} G.val H.val then f H else 0) =
      c * (if SameFiber {i,j} G.val H.val then gatedCentered i j k l H else 0)
    rw [ite_eq_left h, ite_eq_left h, hc H h]
    change c * (if active i j k l G then _ else 0) =
      c * (if active i j k l H then _ else 0)
    rw [active_sameFiber i j k l hij h]
  · simp [restrictCell, localizedVector, h]

theorem projection_localization (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (f : StateSpace n d) :
    (Submodule.span ℝ {localizedVector i j k l G}).starProjection f =
      restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f) := by
  let z := localizedVector i j k l G
  let P := Submodule.span ℝ {z}
  have hz : z ∈ equalitySpace i j k l := localizedVector_mem i j k l hij G
  have hr : projection i j k l f ∈ equalitySpace i j k l :=
    (equalitySpace i j k l).starProjection_apply_mem f
  obtain ⟨c,hc⟩ := restrict_eq_smul_localizedVector i j k l hij G _ hr
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hc]
    exact Submodule.smul_mem P c (Submodule.subset_span (Set.mem_singleton z))
  · intro w hw
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ht, inner_smul_right]
    suffices hzero : ⟪f - restrictCell (fun H => SameFiber {i,j} G.val H.val)
        (projection i j k l f), z⟫ = 0 by rw [hzero, mul_zero]
    have horth := (equalitySpace i j k l).starProjection_inner_eq_zero f z hz
    change ⟪f - projection i j k l f, z⟫ = 0 at horth
    rw [← horth, state_inner, state_inner]
    apply Finset.sum_congr rfl
    intro H hH
    by_cases h : SameFiber {i,j} G.val H.val
    · simp [restrictCell, h]
    · simp [z, localizedVector, restrictCell, h]

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SliceMoments

variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

theorem average_containment (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) (hCq : C.card ≤ q) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hdenC : (U.card.choose C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hCq.trans hq)).ne'
  have hmul := Nat.choose_mul (n := U.card) hCq
  have hmulR : (U.card.choose q : ℝ) * (q.choose C.card : ℝ) =
      (U.card.choose C.card : ℝ) * ((U.card - C.card).choose (q - C.card) : ℝ) := by
    exact_mod_cast hmul
  unfold average
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter_powersetCard_subset C U q hCU hCq]
  apply (div_eq_div_iff hden hdenC).mpr
  nlinarith

theorem average_containment_all (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  by_cases hCq : C.card ≤ q
  · exact average_containment U C q hCU hq hCq
  · have hlt : q < C.card := by omega
    have hempty : (U.powersetCard q).filter (C ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hCS
      have hcard := Finset.card_le_card hCS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      omega
    unfold average
    rw [← Finset.sum_filter, hempty]
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem average_coord (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i : V) (hi : i ∈ U) :
    average U q (coord i) = (q : ℝ) / U.card := by
  change average U q (fun S => if i ∈ S then 1 else 0) = _
  simpa using average_containment_all U {i} q
    (Finset.singleton_subset_iff.mpr hi) hq

theorem average_coord_mul (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => coord i S * coord j S) =
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
  have hpair : ({i, j} : Finset V).card = 2 := by simp [hne]
  have hCU : ({i, j} : Finset V) ⊆ U := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  have hfun : (fun S => coord i S * coord j S) =
      (fun S : Finset V => if ({i, j} : Finset V) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;> simp [coord, Finset.insert_subset_iff, Finset.singleton_subset_iff, hiS, hjS]
  rw [hfun, average_containment_all U {i, j} q hCU hq, hpair,
    Nat.cast_choose_two, Nat.cast_choose_two]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

theorem equalIndicator_eq (i j : V) (S : Finset V) :
    equalIndicator i j S = 1 - coord i S - coord j S + 2 * (coord i S * coord j S) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [equalIndicator, coord, hi, hj]

theorem average_equalIndicator (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (equalIndicator i j) = equalMean U q := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hf : equalIndicator i j =
      (fun S => 1 - coord i S - coord j S + 2 * (coord i S * coord j S)) := by
    funext S
    exact equalIndicator_eq i j S
  rw [hf, average_add, average_sub, average_sub, average_const U q hq 1,
    average_coord U q hq i hi, average_coord U q hq j hj,
    average_mul_left, average_coord_mul U q hq i j hi hj hne]
  unfold equalMean
  field_simp
  ring

end Problem315.SliceMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualitySlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem observable_eq_equalIndicator (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) :
    observable i k l G = SliceMoments.equalIndicator k l (leftSet G.val i j) := by
  have hk := (mem_singletonSet G.val i j k).mp ha.1
  have hl := (mem_singletonSet G.val i j l).mp ha.2
  have hkl : (k ∈ leftSet G.val i j) ↔ G.val.Adj i k := by
    rw [mem_leftSet]
    simp only [hk.1, true_and]
    rcases hk.2 with h | h <;> tauto
  have hll : (l ∈ leftSet G.val i j) ↔ G.val.Adj i l := by
    rw [mem_leftSet]
    simp only [hl.1, true_and]
    rcases hl.2 with h | h <;> tauto
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = _
  simp only [SliceMoments.equalIndicator, hkl, hll]

theorem assignment_sum (G : GraphState n d) (i j : Fin n)
    (f : Finset (Fin n) → ℝ) :
    (∑ T : Assignment G.val i j, f T.val) =
      ∑ T ∈ (singletonSet G.val i j).powersetCard (leftSet G.val i j).card, f T := by
  let e : Assignment G.val i j ≃
      ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card) :=
    { toFun := fun T => ⟨T.val, Finset.mem_powersetCard.mpr T.property⟩
      invFun := fun T => ⟨T.val, Finset.mem_powersetCard.mp T.property⟩
      left_inv := fun T => by apply Subtype.ext; rfl
      right_inv := fun T => by apply Subtype.ext; rfl }
  calc
    _ = ∑ T : ↥((singletonSet G.val i j).powersetCard (leftSet G.val i j).card),
        f T.val := e.sum_comp (fun T => f T.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem reconstructed_sameFiber (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) :
    SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val := by
  apply (sameFiber_iff_key_eq i j hij _ _).mpr
  exact ((stateFiberEquiv G i j hij).symm T).property.symm

theorem observable_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (ha : active i j k l G) (T : Assignment G.val i j) :
    observable i k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.equalIndicator k l T.val := by
  have hA := (active_sameFiber i j k l hij (reconstructed_sameFiber G i j hij T)).mp ha
  rw [observable_eq_equalIndicator i j k l _ hA]
  rw [stateFiberEquiv_symm_apply, leftSet_trade]

theorem expectation_observable_eq_mean (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G) :
    expectation n d {i,j} (observable i k l) G =
      SliceMoments.equalMean (singletonSet G.val i j) (leftSet G.val i j).card := by
  rw [expectation_eq_assignment_average G i j hij]
  simp_rw [observable_reconstruction G i j k l hij ha]
  rw [assignment_sum]
  exact SliceMoments.average_equalIndicator _ _
    (Finset.card_le_card (leftSet_subset_singletonSet G.val i j)) k l ha.1 ha.2 hkl

theorem centered_reconstruction (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (ha : active i j k l G)
    (T : Assignment G.val i j) :
    centered i j k l ((stateFiberEquiv G i j hij).symm T).val =
      SliceMoments.centeredEqual (singletonSet G.val i j)
        (leftSet G.val i j).card k l T.val := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l ((stateFiberEquiv G i j hij).symm T).val -
    expectation n d {i,j} (observable i k l) ((stateFiberEquiv G i j hij).symm T).val = _
  rw [observable_reconstruction G i j k l hij ha]
  rw [(expectation_mem {i,j} (observable i k l)) _ G
    (reconstructed_sameFiber G i j hij T).symm]
  rw [expectation_observable_eq_mean G i j k l hij hkl ha]
  rfl

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

private theorem sum_assignment_reconstruct (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) =
      ∑ H ∈ fiberStates {i,j} G, f H := by
  calc
    _ = ∑ H : ↥(fiberStates {i,j} G), f H.val :=
      (resamplingFiberEquiv G i j hij).symm.sum_comp (fun H => f H.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem assignmentRestriction_inner_supported (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f z : StateSpace n d)
    (hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0) :
    ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ⟪f,z⟫ := by
  rw [state_inner]
  have hinner : ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ∑ T : Assignment G.val i j,
        f ((stateFiberEquiv G i j hij).symm T).val *
          z ((stateFiberEquiv G i j hij).symm T).val := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hinner, sum_assignment_reconstruct G i j hij (fun H => f H * z H)]
  unfold fiberStates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases h : SameFiber {i,j} G.val H.val
  · simp only [ite_eq_left h]
  · simp [h, hz H h]

theorem restriction_localizedVector (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    assignmentRestriction G i j hij (localizedVector i j k l G) =
      assignmentVector G i j k l := by
  ext T
  rw [assignmentRestriction_apply]
  have h := reconstructed_sameFiber G i j hij T
  have ha := active_sameFiber i j k l hij h
  change (if SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val then
    (if active i j k l ((stateFiberEquiv G i j hij).symm T).val then
      centered i j k l ((stateFiberEquiv G i j hij).symm T).val else 0) else 0) = _
  rw [ite_eq_left h, ← ha]
  by_cases hA : active i j k l G
  · simpa only [assignmentVector, WithLp.toLp_ofLp, ite_eq_left hA] using
      centered_reconstruction G i j k l hij hkl hA T
  · simp [assignmentVector, hA]

theorem assignmentRestriction_projection (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) =
      (Submodule.span ℝ {assignmentVector G i j k l}).starProjection
        (assignmentRestriction G i j hij f) := by
  let z := localizedVector i j k l G
  have hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0 := by
    intro H hH
    simp [z, localizedVector, restrictCell, hH]
  have hlocal := projection_localization i j k l hij G f
  have hrestrict := congrArg (assignmentRestriction G i j hij) hlocal
  have hcell : assignmentRestriction G i j hij
      (restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f)) =
      assignmentRestriction G i j hij (projection i j k l f) := by
    ext T
    simp only [assignmentRestriction_apply, restrictCell_apply,
      ite_eq_left (reconstructed_sameFiber G i j hij T)]
  rw [hcell] at hrestrict
  rw [← hrestrict, Submodule.starProjection_singleton, map_smul,
    restriction_localizedVector G i j k l hij hkl, Submodule.starProjection_singleton]
  congr 1
  have hi := assignmentRestriction_inner_supported G i j hij f z hz
  have hn := assignmentRestriction_inner_supported G i j hij z z hz
  rw [restriction_localizedVector G i j k l hij hkl] at hi hn
  rw [real_inner_comm] at hi
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
  rw [hi, hn]
  congr 1
  exact real_inner_comm _ _

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEqualityTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

attribute [local instance] Classical.propDecidable

theorem stateFiberNormalizedEquiv_mem {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (H : StateFiber G i j) (x : singletonSet G.val i j) :
    x ∈ (stateFiberNormalizedEquiv G i j hij H).val ↔
      H.val.val.Adj i x.val := by
  change x ∈ (leftSet H.val.val i j).subtype
    (fun z => z ∈ singletonSet G.val i j) ↔ _
  rw [Finset.mem_subtype, mem_leftSet]
  have hx : x.val ∈ singletonSet H.val.val i j := by
    rw [singletonSet_eq_of_key_eq H.property]
    exact x.property
  obtain ⟨hxo, hxor⟩ := (mem_singletonSet H.val.val i j x.val).mp hx
  rcases hxor with ht | ht <;> simp_all

theorem raw_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
      if x = y then 0 else
        (if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) -
          SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
            (leftSet G.val i j).card := by
  simp only [SliceNormalized.raw,
    SliceMoments.centeredEqual, SliceMoments.equalIndicator,
    stateFiberNormalizedEquiv_mem]

theorem equalIndicator_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceMoments.equalIndicator x y (stateFiberNormalizedEquiv G i j hij H).val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0 := by
  simp only [SliceMoments.equalIndicator, stateFiberNormalizedEquiv_mem]

theorem stateFiber_average_equality {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  let e := stateFiberNormalizedEquiv G i j hij
  have hs : (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) =
      ∑ S : SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card,
        SliceMoments.equalIndicator x y S.val := by
    apply Fintype.sum_equiv e
    intro H
    exact (equalIndicator_stateFiberNormalizedEquiv G i j hij x y H).symm
  rw [hs]
  have hq : (leftSet G.val i j).card ≤
      (Finset.univ : Finset (singletonSet G.val i j)).card := by
    simpa using Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have hm := SliceMoments.average_equalIndicator
    (Finset.univ : Finset (singletonSet G.val i j)) (leftSet G.val i j).card hq
    x y (Finset.mem_univ x) (Finset.mem_univ y) hxy
  simpa only [SliceMoments.average, Finset.sum_coe_sort, Finset.card_univ,
    Fintype.card_coe] using hm

theorem stateFiber_sum_eq_fiberStates {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j, f H.val) =
      ∑ H ∈ PairResampling.fiberStates {i, j} G, f H := by
  let e : StateFiber G i j ≃ PairResampling.fiberStates {i, j} G :=
    { toFun H := ⟨H.val, (PairResampling.mem_fiberStates {i, j} G H.val).mpr
        ((sameFiber_iff_key_eq i j hij G.val H.val.val).mpr H.property.symm)⟩
      invFun H := ⟨H.val, ((sameFiber_iff_key_eq i j hij G.val H.val.val).mp
        ((PairResampling.mem_fiberStates {i, j} G H.val).mp H.property)).symm⟩
      left_inv H := by apply Subtype.ext; rfl
      right_inv H := by apply Subtype.ext; rfl }
  calc
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f (e.symm H).val :=
      (Equiv.sum_comp e.symm (fun H : StateFiber G i j => f H.val)).symm
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f H.val := rfl
    _ = _ := Finset.sum_coe_sort _ _

theorem expectation_eq_equalMean_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) :
    PairResampling.expectation n d {i, j} f G =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij,
    ← stateFiber_sum_eq_fiberStates G i j hij]
  simp_rw [hf]
  exact stateFiber_average_equality G i j hij x y hxy

theorem fluctuation_eq_raw_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0)
    (H : StateFiber G i j) :
    PairResampling.fluctuation n d {i, j} f H.val =
      SliceNormalized.raw (leftSet G.val i j).card x y
        (stateFiberNormalizedEquiv G i j hij H) := by
  have hexp : PairResampling.expectation n d {i, j} f H.val =
      PairResampling.expectation n d {i, j} f G :=
    PairResampling.expectation_mem {i, j} f H.val G
      ((sameFiber_iff_key_eq i j hij H.val.val G.val).mpr H.property)
  rw [PairResampling.fluctuation_eq_sub]
  change f H.val - PairResampling.expectation n d {i, j} f H.val = _
  rw [hexp, expectation_eq_equalMean_of_fiber G i j hij x y hxy f hf,
    hf H, raw_stateFiberNormalizedEquiv]
  simp only [hxy, ite_false]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSwapFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

theorem reverse_fourVertexProposal {n : ℕ} (i u v j : Fin n)
    (h : FourDistinct i u v j) (hr : FourDistinct i v u j) :
    reverseProposal (fourVertexProposal i u v j h) = fourVertexProposal i v u j hr := by
  apply SwitchProposal.ext_matchings
  · ext x y
    simp only [removedMatching_reverse, addedMatching_fourVertexProposal,
      removedMatching_fourVertexProposal]
  · ext x y
    simp only [addedMatching_reverse, removedMatching_fourVertexProposal,
      addedMatching_fourVertexProposal]

theorem valid_fourVertex_iff_left_membership {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j) :
    validSwitch G.val (fourVertexProposal i u v j h) ↔
      u ∈ leftSet G.val i j ∧ v ∉ leftSet G.val i j := by
  rw [validSwitch_fourVertexProposal_iff]
  obtain ⟨huo, huadj⟩ := (mem_singletonSet G.val i j u).mp hu
  obtain ⟨hvo, hvadj⟩ := (mem_singletonSet G.val i j v).mp hv
  simp only [mem_leftSet, huo, hvo, true_and]
  constructor
  · rintro ⟨hiu, hvj, hiv, huj⟩
    exact ⟨⟨hiu, fun hju => huj hju.symm⟩, fun hh => hiv hh.1⟩
  · rintro ⟨⟨hiu, hju⟩, hvl⟩
    have hr : G.val.Adj j v ∧ ¬ G.val.Adj i v := hvadj.resolve_left hvl
    exact ⟨hiu, hr.1.symm, hr.2, fun huj => hju huj.symm⟩

theorem state_eq_bidirectional_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = (leftSet G.val i j).map (Equiv.swap u v).toEmbedding) :
    H = if validSwitch G.val (fourVertexProposal i u v j h) then
      proposalState G (fourVertexProposal i u v j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) then
      proposalState G (reverseProposal (fourVertexProposal i u v j h)) else G := by
  classical
  let hr : FourDistinct i v u j :=
    ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩
  rw [reverse_fourVertexProposal i u v j h hr]
  have hp := valid_fourVertex_iff_left_membership G i u v j h hu hv
  have hq := valid_fourVertex_iff_left_membership G i v u j hr hv hu
  have hforward (hvl : u ∈ leftSet G.val i j) (hvr : v ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i u v j h) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i u v j h).mp
      (hp.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i u v j h).val i j
      rw [hleft, map_swap_eq_exchange _ u v hvl hvr,
        fourVertexState_leftSet G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hreverse (hvl : v ∈ leftSet G.val i j) (hvr : u ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i v u j hr) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i v u j hr).mp
      (hq.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i v u j hr).val i j
      rw [hleft, Equiv.swap_comm u v, map_swap_eq_exchange _ v u hvl hvr,
        fourVertexState_leftSet G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hfixed (hh : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : H = G := by
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hh]
  by_cases hul : u ∈ leftSet G.val i j <;> by_cases hvl : v ∈ leftSet G.val i j
  · rw [ite_eq_right (by simp only [hp, hul, hvl, not_true_eq_false, and_false, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hul, hvl, not_true_eq_false, and_false, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])
  · rw [ite_eq_left (hp.mpr ⟨hul, hvl⟩)]
    exact hforward hul hvl
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_left (hq.mpr ⟨hvl, hul⟩)]
    exact hreverse hvl hul
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hvl, false_and, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])

theorem assignmentRelabel_swap_eq_bidirectional {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let p := fourVertexProposal i x.val y.val j h
    if validSwitch H.val p then proposalState H p
    else if validSwitch H.val (reverseProposal p) then
      proposalState H (reverseProposal p) else H := by
  classical
  let H : GraphState n d := ((stateFiberEquiv G i j hij).symm T).val
  let K : GraphState n d := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val :=
    leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j = T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply state_eq_bidirectional_of_key_leftSet_swap H K i x.val y.val j h
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]

theorem fourDistinct_of_singleton_labels {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G i j) (hxy : x ≠ y) :
    FourDistinct i x.val y.val j := by
  have hx := ((mem_singletonSet G i j x.val).mp x.property).1
  have hy := ((mem_singletonSet G i j y.val).mp y.property).1
  exact ⟨hx.1.symm, hy.1.symm, hij,
    fun hval => hxy (Subtype.ext hval), hx.2, hy.2⟩

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSwapFlipProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem assignmentRelabel_swap_eq_flip
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    SwitchFlip.flip (fourVertexProposal i x.val y.val j h)
      ((stateFiberEquiv G i j hij).symm T).val :=
  assignmentRelabel_swap_eq_bidirectional G i j hij x y h T

theorem projection_at_assignment
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (f : PairResampling.StateSpace n d) (T : Assignment G.val i j) :
    SwitchFlip.projection (fourVertexProposal i x.val y.val j h) f
      ((stateFiberEquiv G i j hij).symm T).val =
    (f ((stateFiberEquiv G i j hij).symm T).val -
      f ((stateFiberEquiv G i j hij).symm
        (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) / 2 := by
  rw [SwitchFlip.projection_apply, assignmentRelabel_swap_eq_flip]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceCardEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

 theorem cardSliceEquiv_relabel (q : ℕ) (σ : Equiv.Perm V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.relabel q σ S) =
      SlicePermutationAction.relabel σ (cardSliceEquiv q S) := by
  apply Subtype.ext
  simp [SlicePermutationAction.relabel, Finset.map_eq_image]

 theorem cardSliceEquiv_swap (q : ℕ) (i j : V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j S) =
      SlicePermutationAction.relabel (Equiv.swap i j) (cardSliceEquiv q S) :=
  cardSliceEquiv_relabel q (Equiv.swap i j) S

include sectionFintypeΩ in
 theorem conjugated_swap_cardSlice {q : ℕ} (e : Ω ≃ SlicePermutationAction.Slice V q)
    (i j : V) (ω : Ω) :
    (e.trans (cardSliceEquiv q).symm).symm
      (SliceEuclideanGenerator.swapState q i j ((e.trans (cardSliceEquiv q).symm) ω)) =
      e.symm (SlicePermutationAction.relabel (Equiv.swap i j) (e ω)) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  change e.symm (cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j
    ((cardSliceEquiv q).symm (e ω)))) = _
  rw [cardSliceEquiv_swap, Equiv.apply_symm_apply]

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem assignmentVector_eq_raw (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    assignmentVector G i j x.val y.val =
      SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y := by
  have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have ha : active i j x.val y.val G := ⟨x.property, y.property⟩
  ext T
  let H := (stateFiberEquiv G i j hij).symm T
  have hc := centered_reconstruction G i j x.val y.val hij hval ha T
  have hr := fluctuation_eq_raw_of_fiber G i j hij x y hxy
    (observable i x.val y.val) (fun _ => rfl) H
  change centered i j x.val y.val H.val = _ at hr
  change (if active i j x.val y.val G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      x.val y.val T.val else 0) = _
  rw [ite_eq_left ha, ← hc]
  change centered i j x.val y.val H.val = _
  rw [hr]
  change SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
    SliceNormalized.raw (leftSet G.val i j).card x y (assignmentNormalizedEquiv G i j T)
  have he : stateFiberNormalizedEquiv G i j hij H = assignmentNormalizedEquiv G i j T := by
    change (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)
      (stateFiberEquiv G i j hij ((stateFiberEquiv G i j hij).symm T)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]

theorem restriction_projection_energy_eq_raw (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    (if x = y then 0 else
      ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) =
    ‖(ℝ ∙ SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x y).starProjection
      (assignmentRestriction G i j hij f)‖ ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hz : SliceNormalized.reindexedRaw (assignmentNormalizedEquiv G i j) x x = 0 := by
      ext T
      simp
    simp [hz]
  · rw [ite_eq_right hxy, assignmentRestriction_projection G i j x.val y.val hij
      (fun h => hxy (Subtype.ext h)), assignmentVector_eq_raw G i j hij x y hxy]

theorem assignment_projection_budget (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) :
    (∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  have hq : (leftSet G.val i j).card ≤ Fintype.card (singletonSet G.val i j) := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have h := SliceNormalized.reindexed_projection_energy_le_swap_sum
    (assignmentNormalizedEquiv G i j) hq (assignmentRestriction G i j hij f)
  have hswap (x y : singletonSet G.val i j) (T : Assignment G.val i j) :
      (assignmentNormalizedEquiv G i j).symm
        (SliceEuclideanGenerator.swapState (leftSet G.val i j).card x y
          (assignmentNormalizedEquiv G i j T)) =
        assignmentRelabel G.val i j (Equiv.swap x y) T := by
    exact SliceNormalized.conjugated_swap_cardSlice (assignmentSliceEquiv G.val i j) x y T
  simp_rw [hswap, assignmentRestriction_apply] at h
  simp_rw [restriction_projection_energy_eq_raw G i j hij]
  linarith

theorem assignmentRestriction_projection_eq_zero_of_inactive
    (G : GraphState n d) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : ¬ active i j k l G) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) = 0 := by
  rw [assignmentRestriction_projection G i j k l hij hkl]
  have hz : assignmentVector G i j k l = 0 := by
    ext T
    simp [assignmentVector, ha]
  simp [hz]

theorem sum_array_subtype {V : Type*} [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) :
    (∑ k : s, ∑ l : s, F k.val l.val) = ∑ k ∈ s, ∑ l ∈ s, F k l := by
  calc
    _ = ∑ k : s, ∑ l ∈ s, F k.val l := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_coe_sort s (fun l => F k.val l)
    _ = _ := Finset.sum_coe_sort s (fun k => ∑ l ∈ s, F k l)

theorem sum_array_eq_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ)
    (hs : ∀ k l, ¬ (k ∈ s ∧ l ∈ s) → F k l = 0) :
    (∑ k, ∑ l, F k l) = ∑ k : s, ∑ l : s, F k.val l.val := by
  calc
    _ = ∑ k ∈ s, ∑ l, F k l := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro k _ hk
      apply Finset.sum_eq_zero
      intro l _
      exact hs k l (fun h => hk h.1)
    _ = ∑ k ∈ s, ∑ l ∈ s, F k l := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro l _ hl
      exact hs k l (fun h => hl h.2)
    _ = _ := (sum_array_subtype s F).symm

theorem assignment_projection_sum_eq_singletons (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) =
    ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
      if x = y then 0 else
        ‖assignmentRestriction G i j hij (projection i j x.val y.val f)‖ ^ 2 := by
  have h := sum_array_eq_subtype (singletonSet G.val i j)
    (fun k l => if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ?_
  · simpa only [Subtype.ext_iff] using h
  · intro k l ha
    by_cases hkl : k = l
    · simp [hkl]
    · rw [ite_eq_right hkl, assignmentRestriction_projection_eq_zero_of_inactive
        G i j k l hij hkl ha f]
      simp

theorem sum_assignmentRestriction_norm_sq (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ G : GraphState n d, ‖assignmentRestriction G i j hij f‖ ^ 2 /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ‖f‖ ^ 2 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [assignmentRestriction_apply]
  have hav (G : GraphState n d) := assignment_average_eq_fiber_average G i j hij
    (fun H => (f H)^2)
  simp_rw [hav]
  exact sum_fiber_average {i,j} (fun H => (f H)^2)

theorem sum_assignmentRestriction_family_norm_sq
    {A : Type*} [Fintype A] (i j : Fin n) (hij : i ≠ j)
    (F : A → StateSpace n d) :
    (∑ G : GraphState n d, (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) /
      (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ)) =
      ∑ a, ‖F a‖ ^ 2 := by
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  simp_rw [sum_assignmentRestriction_norm_sq i j hij]

theorem sum_norm_sq_le_of_assignment_restriction_budget
    {A B : Type*} [Fintype A] [Fintype B]
    (i j : Fin n) (hij : i ≠ j) (F : A → StateSpace n d) (H : B → StateSpace n d)
    (hl : ∀ G : GraphState n d,
      (∑ a, ‖assignmentRestriction G i j hij (F a)‖ ^ 2) ≤
        ∑ b, ‖assignmentRestriction G i j hij (H b)‖ ^ 2) :
    (∑ a, ‖F a‖ ^ 2) ≤ ∑ b, ‖H b‖ ^ 2 := by
  rw [← sum_assignmentRestriction_family_norm_sq i j hij F,
    ← sum_assignmentRestriction_family_norm_sq i j hij H]
  apply Finset.sum_le_sum
  intro G _
  exact div_le_div_of_nonneg_right (hl G) (Nat.cast_nonneg _)

@[simp] theorem orderedGain_of_distinct (i j k l : Fin n)
    (h : FourDistinct i k l j) :
    orderedGain (d := d) i j k l =
      SwitchFlip.projection (fourVertexProposal i k l j h) := by
  simp only [orderedGain, dite_eq_left h]

theorem assignment_orderedGain_norm_sq (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G.val i j)
    (f : StateSpace n d) :
    ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val -
          f ((stateFiberEquiv G i j hij).symm
            (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  by_cases hxy : x = y
  · subst y
    have hd : ¬ FourDistinct i x.val x.val j := fun h => h.2.2.2.1 rfl
    simp [orderedGain, hd, assignmentRelabel, SlicePermutationAction.relabel]
  · have hd := fourDistinct_of_singleton_labels G.val i j hij x y hxy
    rw [orderedGain_of_distinct i j x.val y.val hd, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [assignmentRestriction_apply, projection_at_assignment G i j hij x y hd]
    ring

theorem sum_array_subtype_le {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (F : V → V → ℝ) (hF : ∀ k l, 0 ≤ F k l) :
    (∑ k : s, ∑ l : s, F k.val l.val) ≤ ∑ k, ∑ l, F k l := by
  rw [sum_array_subtype]
  calc
    _ ≤ ∑ k ∈ s, ∑ l, F k l := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro l _ _
      exact hF k l
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro k _ _
      exact Finset.sum_nonneg (fun l _ => hF k l)

theorem assignment_ordered_projection_budget (G : GraphState n d)
    (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else
      ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2) ≤
      ∑ k, ∑ l, ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2 := by
  rw [assignment_projection_sum_eq_singletons G i j hij f]
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ∑ T : Assignment G.val i j,
          (f ((stateFiberEquiv G i j hij).symm T).val -
            f ((stateFiberEquiv G i j hij).symm
              (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 :=
      assignment_projection_budget G i j hij f
    _ = ∑ x : singletonSet G.val i j, ∑ y : singletonSet G.val i j,
        ‖assignmentRestriction G i j hij (orderedGain i j x.val y.val f)‖ ^ 2 := by
      simp_rw [assignment_orderedGain_norm_sq G i j hij]
      simp only [Finset.mul_sum]
    _ ≤ _ := sum_array_subtype_le (singletonSet G.val i j)
      (fun k l => ‖assignmentRestriction G i j hij (orderedGain i j k l f)‖ ^ 2)
      (fun k l => sq_nonneg _)

theorem ordered_projection_budget (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    (∑ k, ∑ l, if k = l then 0 else ‖projection i j k l f‖ ^ 2) ≤
      ∑ k, ∑ l, ‖orderedGain i j k l f‖ ^ 2 := by
  let F : Fin n × Fin n → StateSpace n d :=
    fun p => if p.1 = p.2 then 0 else projection i j p.1 p.2 f
  let H : Fin n × Fin n → StateSpace n d := fun p => orderedGain i j p.1 p.2 f
  have hF (G : GraphState n d) (k l : Fin n) :
      ‖assignmentRestriction G i j hij (F (k,l))‖ ^ 2 =
        if k = l then 0 else
          ‖assignmentRestriction G i j hij (projection i j k l f)‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  have h := sum_norm_sq_le_of_assignment_restriction_budget i j hij F H (fun G => by
    simp only [Fintype.sum_prod_type]
    simp_rw [hF]
    exact assignment_ordered_projection_budget G i j hij f)
  have hFg (k l : Fin n) : ‖F (k,l)‖ ^ 2 =
      if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
    by_cases hkl : k = l <;> simp [F, hkl]
  simpa only [Fintype.sum_prod_type, hFg, H] using h

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.UnorderedPairSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.UnorderedPairSums

variable {V : Type*} [DecidableEq V]

theorem ordered_fiber (s : Finset V) (i j : V)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    s.offDiag.filter (fun p => ({p.1,p.2} : Finset V) = {i,j}) =
      {(i,j),(j,i)} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hp,he⟩
    have hs : ({p.1,p.2} : Set V) = {i,j} := by
      simpa only [Finset.coe_pair] using congrArg (fun t : Finset V => (t : Set V)) he
    rcases Set.pair_eq_pair_iff.mp hs with hp | hp
    · exact Or.inl (Prod.ext hp.1 hp.2)
    · exact Or.inr (Prod.ext hp.1 hp.2)
  · rintro (rfl | rfl) <;> simp [hi,hj,hij,hij.symm, Finset.pair_comm]

theorem sum_offDiag_eq_two_mul (s : Finset V) (f : Finset V → ℝ) :
    (∑ p ∈ s.offDiag, f {p.1,p.2}) = 2 * ∑ a ∈ s.powersetCard 2, f a := by
  have hmap (p : V × V) (hp : p ∈ s.offDiag) :
      ({p.1,p.2} : Finset V) ∈ s.powersetCard 2 := by
    obtain ⟨hi,hj,hij⟩ := Finset.mem_offDiag.mp hp
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    · simp [hij]
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨has, hac⟩ := Finset.mem_powersetCard.mp ha
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hac
  have hi := has (Finset.mem_insert_self i {j})
  have hj := has (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  rw [ordered_fiber s i j hi hj hij]
  have hp : (i,j) ≠ (j,i) := fun h => hij (congrArg Prod.fst h)
  simp [hp, two_mul]

theorem sum_ordered_eq_two_mul [Fintype V] (f : Finset V → ℝ) :
    (∑ i : V, ∑ j : V, if i ≠ j then f {i,j} else 0) =
      2 * ∑ a ∈ (Finset.univ : Finset V).powersetCard 2, f a := by
  have he : (Finset.univ : Finset V).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V => p.1 ≠ p.2) := by
    ext p
    simp [Finset.mem_offDiag]
  have h := sum_offDiag_eq_two_mul (Finset.univ : Finset V) f
  rw [he, Finset.sum_filter, Finset.sum_product] at h
  exact h

end Problem315.UnorderedPairSums

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityUnorderedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem sum_pairProjection_eq_half_ordered (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖pairProjection {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖pairProjection {i,j} {k,l} f‖ ^ 2 else 0) =
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl, ite_eq_left hkl, pairProjection_pair i j k l hij hkl]
    · rw [ite_eq_right hkl, ite_eq_right hkl]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖pairProjection {i,j} b f‖ ^ 2) = _
  linarith

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityBudgetUnordered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem orderedGain_eq_gain (i j k l : Fin n) :
    orderedGain (d := d) i j k l = CrossToggle.gain {i,j} {k,l} :=
  (CrossToggle.gain_pair_eq_ordered i j k l).symm

theorem sum_gain_eq_half_ordered (i j : Fin n) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖CrossToggle.gain {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n, ‖orderedGain i j k l f‖ ^ 2 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖CrossToggle.gain {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖CrossToggle.gain {i,j} {k,l} f‖ ^ 2 else 0) =
        ‖orderedGain i j k l f‖ ^ 2 := by
    rw [orderedGain_eq_gain]
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl]
    · have hkl' : k = l := not_ne_iff.mp hkl
      subst l
      simp [CrossToggle.gain]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖CrossToggle.gain {i,j} b f‖ ^ 2) = _
  linarith

theorem pair_projection_budget (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection a b f‖ ^ 2) ≤
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
  by_cases ha : a.card = 2
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
    rw [sum_pairProjection_eq_half_ordered i j hij f, sum_gain_eq_half_ordered i j f]
    have h := ordered_projection_budget i j hij f
    have he (k l : Fin n) :
        (if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0) =
        if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
      by_cases hkl : k = l <;> simp [hkl]
    simp_rw [he]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  · have hz (b : Finset (Fin n)) : pairProjection (d := d) a b = 0 :=
      pairProjection_eq_zero_left a b ha
    simp only [hz, zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_chain_main_oai :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) := by
  intro n d hn hd hgraph
  apply switch_chain_main_of_spectralGap n d hn
  intro hmany
  apply PairResampling.spectralGap_of_triples_and_disjoint hn hgraph
    PairResampling.tripleGenerator_square
  intro f
  exact PairResampling.disjoint_sum_nonneg_of_named_interaction_budget f
    (fun i j k l h => PairEquality.actual_named_interaction i j k l h f)
    (fun a _ => PairEquality.pair_projection_budget a f)

end Problem315

end

end OAI
end

theorem solution : type_of% @OAI.Problem315.switch_chain_main_oai := @OAI.Problem315.switch_chain_main_oai
