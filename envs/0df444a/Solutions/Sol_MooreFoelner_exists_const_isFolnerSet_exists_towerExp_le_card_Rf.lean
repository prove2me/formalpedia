-- Prove2me | solution 1 for MooreFoelner.exists_const_isFolnerSet_exists_towerExp_le_card_Rf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T08:42:22.807976+00:00
-- url     : https://prove2.me/submissions/cd1fcf1e-767e-4559-a09b-a8d40ed539d9

import Theorems.Thm_MooreFoelner_two_zpow_card_delta_sub_two_lt_card
import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
import Theorems.Thm_MooreFoelner_exists_const_isWeightedFolner_trees
import Theorems.Thm_MooreFoelner_exists_const_isWeightedFolner_delta
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §5 end (group Goal): Claim 5.14, Theorem 1.1 and its "in particular", and the
F-amenability reference goal
-/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

/-! ## Generic facts about (weighted) Følner sets -/

theorem isWeightedFolner_mono {G S : Type*} [Group G] {act : S → G → Option S} {Γ : Finset G}
    {μ : S →₀ ℝ} {ε ε' : ℝ} (h : IsWeightedFolner act Γ μ ε) (hle : ε ≤ ε') :
    IsWeightedFolner act Γ μ ε' := by
  refine ⟨h.1, lt_of_lt_of_le h.2 ?_⟩
  have : 0 ≤ mass μ Set.univ := Finset.sum_nonneg (fun s _ => h.1 s)
  exact mul_le_mul_of_nonneg_right hle this

theorem exists_pos_of_isWeightedFolner {G S : Type*} [Group G] {act : S → G → Option S}
    {Γ : Finset G} {μ : S →₀ ℝ} {ε : ℝ} (h : IsWeightedFolner act Γ μ ε) : ∃ s, 0 < μ s := by
  by_contra hne
  push Not at hne
  have h0 : ∀ s, μ s = 0 := fun s => le_antisymm (hne s) (h.1 s)
  have hm : mass μ Set.univ = 0 := Finset.sum_eq_zero (fun s _ => h0 s)
  have hnn : 0 ≤ ∑ γ ∈ Γ, ∑ᶠ s, |valAt act μ s γ - μ s| :=
    Finset.sum_nonneg (fun _ _ => finsum_nonneg (fun _ => abs_nonneg _))
  have := h.2
  rw [hm, mul_zero] at this
  linarith

theorem nonempty_of_isFolnerSet {G : Type*} [Group G] {Γ A : Finset G} {ε : ℝ}
    (h : IsFolnerSet Γ A ε) : A.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  unfold IsFolnerSet at h
  simp at h

/-! ## Trees -/

theorem nonempty_of_isTree {T : Finset Seq} (hT : IsTree T) : T.Nonempty := by
  obtain ⟨t, ⟨ht, _⟩, _⟩ := hT (fun _ => false)
  exact ⟨t, ht⟩

theorem isTreeDiagram_Lf_Rf (f : MooreF) : IsTreeDiagram (Lf (toMap f)) (Rf (toMap f)) :=
  (bijOn_Lf_Rf_and_diagramMul.2.2.2.2.2.2.1 f).1

theorem delta_spec {T : Finset Seq} (h : delta T ≠ trivialTree) :
    IsTree (delta T) ∧ DeltaConditions T (delta T) := by
  unfold delta at h ⊢
  split_ifs at h ⊢ with hex
  · exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2.2.1⟩
  · exact absurd rfl h

theorem four_le_card_of_deltaConditions {T U : Finset Seq} (h : DeltaConditions T U) :
    4 ≤ U.card := by
  obtain ⟨-, -, -, h1, h2⟩ := h
  have hlen : (sorted U).length = U.card := by simp [sorted, List.length_mergeSort]
  have h2le : 2 ≤ (interior U).length := by
    rcases hI : interior U with _ | ⟨u, _ | ⟨v, rest⟩⟩
    · simp [hI] at h1
    · simp [hI] at h1 h2
      rw [h1] at h2
      cases h2
    · simp
  simp only [interior, List.length_dropLast, List.length_drop, hlen] at h2le
  omega

/-! ## The tower function -/

open ThompsonAmenability in
theorem towerExp_succ (p m : ℕ) : towerExp (p + 1) m = 2 ^ towerExp p m := rfl

open ThompsonAmenability in
theorem one_le_towerExp_succ (q : ℕ) : 1 ≤ towerExp (q + 1) 0 := by
  rw [towerExp_succ]; exact Nat.one_le_two_pow

/-! ## Claim 5.14 -/

open ThompsonAmenability in
/-- The induction in the proof of Claim 5.14: applying Lemma 5.13 `m` times to a weighted
`ε`-Følner set of trees with `K^m ε ≤ 1` and reading the sizes back with Lemma 5.4. -/
theorem iter (K C2 : ℝ) (hK : 1 < K) (hC2 : C2 ≤ K)
    (h26 : ∀ (ε : ℝ) (μ : Finset Seq →₀ ℝ), (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → C2 * ε ≤ 1 →
      ∃ ν : Finset Seq →₀ ℝ, IsWeightedFolner treeAct gens ν (C2 * ε) ∧
        ↑ν.support ⊆ {U | ∃ T, 0 < μ T ∧ U = delta T ∧ delta T ≠ trivialTree ∧
          ∀ γ ∈ gens, ActsProperlyOn γ (delta T)}) :
    ∀ (m : ℕ) (ε : ℝ) (μ : Finset Seq →₀ ℝ), 0 < ε → (∀ T ∈ μ.support, IsTree T) →
      IsWeightedFolner treeAct gens μ ε → K ^ m * ε ≤ 1 →
      ∃ T, 0 < μ T ∧ (m = 0 ∨ towerExp (m + 1) 0 + 3 ≤ T.card) := by
  intro m
  induction m with
  | zero =>
    intro ε μ _ _ hμ _
    obtain ⟨T, hT⟩ := exists_pos_of_isWeightedFolner hμ
    exact ⟨T, hT, Or.inl rfl⟩
  | succ m ih =>
    intro ε μ hε htree hμ hKm
    have hK1 : (1 : ℝ) ≤ K := hK.le
    have hKε : K * ε ≤ 1 := by
      have : K ≤ K ^ (m + 1) := le_self_pow₀ hK1 (by omega)
      nlinarith
    have hC2ε : C2 * ε ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hC2 hε.le) hKε
    obtain ⟨ν, hν, hsupp⟩ := h26 ε μ htree hμ hC2ε
    have hν' : IsWeightedFolner treeAct gens ν (K * ε) :=
      isWeightedFolner_mono hν (mul_le_mul_of_nonneg_right hC2 hε.le)
    have hνtree : ∀ U ∈ ν.support, IsTree U := by
      intro U hU
      obtain ⟨T, -, rfl, hne, -⟩ := hsupp hU
      exact (delta_spec hne).1
    have hKm' : K ^ m * (K * ε) ≤ 1 := by rw [← mul_assoc, ← pow_succ]; exact hKm
    obtain ⟨U, hU, hJ⟩ := ih (K * ε) ν (mul_pos (by linarith) hε) hνtree hν' hKm'
    have hUs : U ∈ ν.support := Finsupp.mem_support_iff.mpr hU.ne'
    obtain ⟨T, hT, rfl, hne, -⟩ := hsupp hUs
    refine ⟨T, hT, Or.inr ?_⟩
    have hTtree : IsTree T := htree T (Finsupp.mem_support_iff.mpr hT.ne')
    have h4 := four_le_card_of_deltaConditions (delta_spec hne).2
    have h54 := two_zpow_card_delta_sub_two_lt_card T hTtree
    have h54' : 2 ^ ((delta T).card - 2) < T.card := by
      have hz : ((delta T).card : ℤ) - 2 = (((delta T).card - 2 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega)]; rfl
      rw [hz, zpow_natCast] at h54
      exact_mod_cast h54
    rcases hJ with rfl | hJ
    · -- `m = 0`: `|∂T| ≥ 4`, so `|T| > 4`
      have : 2 ^ 2 ≤ 2 ^ ((delta T).card - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [towerExp]
      norm_num at this ⊢
      omega
    · have ht1 := one_le_towerExp_succ m
      have hpow : 2 ^ (towerExp (m + 1) 0 + 1) ≤ 2 ^ ((delta T).card - 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2t : 2 ≤ 2 ^ towerExp (m + 1) 0 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ towerExp (m + 1) 0 := Nat.pow_le_pow_right (by norm_num) ht1
      rw [towerExp_succ (m + 1)]
      rw [pow_succ] at hpow
      omega

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

/-! ## Word length along a chain, and the generators `x₀, x₁` -/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

namespace ThompsonAmenability

end ThompsonAmenability
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Goal in
theorem solution :
    ∃ K : ℝ, 1 < K ∧ ∀ (n : ℕ) (A : Finset MooreF), IsFolnerSet gens A (K ^ (-(n : ℤ))) →
      ∃ f ∈ A, ThompsonAmenability.towerExp n 0 ≤ (Lf (toMap f)).card ∧
        ThompsonAmenability.towerExp n 0 ≤ (Rf (toMap f)).card := by
  obtain ⟨C1, h18⟩ := exists_const_isWeightedFolner_trees
  obtain ⟨C2, h26⟩ := exists_const_isWeightedFolner_delta
  set K : ℝ := max (max C1 C2) 2 with hKdef
  have hK : 1 < K := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hC1 : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK0 : 0 < K := by linarith
  refine ⟨K, hK, ?_⟩
  intro n A hA
  -- the two trees of a reduced diagram have the same number of leaves
  suffices h : ∃ f ∈ A, ThompsonAmenability.towerExp n 0 ≤ (Rf (toMap f)).card by
    obtain ⟨f, hf, hR⟩ := h
    exact ⟨f, hf, (isTreeDiagram_Lf_Rf f).2.2 ▸ hR, hR⟩
  cases n with
  | zero =>
    obtain ⟨f, hf⟩ := nonempty_of_isFolnerSet hA
    exact ⟨f, hf, by simp [ThompsonAmenability.towerExp]⟩
  | succ m =>
    obtain ⟨μ, hμ, hsupp⟩ := h18 _ A hA
    have hε : C1 * K ^ (-((m + 1 : ℕ) : ℤ)) ≤ K ^ (-(m : ℤ)) := by
      have hpos : 0 < K ^ (-((m + 1 : ℕ) : ℤ)) := zpow_pos hK0 _
      calc C1 * K ^ (-((m + 1 : ℕ) : ℤ)) ≤ K * K ^ (-((m + 1 : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_right hC1 hpos.le
        _ = K ^ (-(m : ℤ)) := by
            rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
            field_simp
    have hμ' := isWeightedFolner_mono hμ hε
    have htree : ∀ T ∈ μ.support, IsTree T := by
      intro T hT
      obtain ⟨f, -, rfl⟩ := hsupp hT
      exact (isTreeDiagram_Lf_Rf f).2.1
    have hKm : K ^ m * K ^ (-(m : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_pos hK0 m).ne']
    obtain ⟨T, hT, hJ⟩ :=
      iter K C2 hK hC2 h26 m (K ^ (-(m : ℤ))) μ (zpow_pos hK0 _) htree hμ' hKm
    obtain ⟨f, hfA, rfl⟩ := hsupp (Finsupp.mem_support_iff.mpr hT.ne')
    refine ⟨f, hfA, ?_⟩
    rcases hJ with rfl | hJ
    · have := (nonempty_of_isTree (isTreeDiagram_Lf_Rf f).2.1).card_pos
      simpa [ThompsonAmenability.towerExp] using this
    · omega
