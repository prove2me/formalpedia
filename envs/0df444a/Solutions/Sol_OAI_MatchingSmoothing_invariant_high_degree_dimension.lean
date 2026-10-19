-- Prove2me | solution 1 for OAI.MatchingSmoothing.invariant_high_degree_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:47:51.146148+00:00
-- url     : https://prove2.me/submissions/88f0fb63-4ba2-4a95-97a4-a13528b7a99a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/RepresentationDimension.lean:L199-L254
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.invariant_high_degree_dimension. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Theorems.Thm_OAI_MatchingSmoothing_Pairing_align_partners
import Theorems.Thm_OAI_MatchingSmoothing_binomial_le_finrank_of_eigenvector_mem
import Theorems.Thm_OAI_MatchingSmoothing_mem_of_fiber_indicators
import Theorems.Thm_OAI_MatchingSmoothing_mul_mem_lowDegree
import Theorems.Thm_OAI_MatchingSmoothing_next_prescribed_sign
import Theorems.Thm_OAI_MatchingSmoothing_simultaneous_sign_eigenvector_preserving

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
variable {E : Type u_1} {X : Type u_2}

lemma lowDegree_mono (x : E → X → ℝ) {d e : ℕ} (h : d ≤ e) :
    lowDegree x d ≤ lowDegree x e := by
  apply Submodule.span_mono
  rintro f ⟨l, hl, hf⟩
  exact ⟨l, hl.trans h, hf⟩

lemma one_mem_lowDegree (x : E → X → ℝ) (d : ℕ) : (1 : X → ℝ) ∈ lowDegree x d :=
  Submodule.subset_span ⟨[], Nat.zero_le _, rfl⟩

lemma coord_mem_lowDegree (x : E → X → ℝ) (e : E) : x e ∈ lowDegree x 1 := by
  apply Submodule.subset_span
  exact ⟨[e], by simp, by simp⟩

lemma prod_mem_lowDegree {ι : Type u_3} (x : E → X → ℝ) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i ∈ s, f i ∈ lowDegree x 1) :
    (∏ i ∈ s, f i) ∈ lowDegree x s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_lowDegree x 0
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.card_insert_of_notMem his]
    have hi := hf i (Finset.mem_insert_self i s)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Nat.add_comm] using mul_mem_lowDegree x hi hs

lemma boolean_pattern_mem_lowDegree [DecidableEq E]
    (x : E → X → ℝ) (s t : Finset E) :
    (∏ e ∈ s, if e ∈ t then x e else 1 - x e) ∈ lowDegree x s.card := by
  apply prod_mem_lowDegree
  intro e _
  split_ifs
  · exact coord_mem_lowDegree x e
  · exact (lowDegree x 1).sub_mem (one_mem_lowDegree x 1) (coord_mem_lowDegree x e)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

lemma exists_internal_edge_compl [Fintype α] [DecidableEq α]
    (M : Pairing α) (U : Finset α) (hU : 2 * U.card < Fintype.card α) :
    ∃ a, a ∉ U ∧ M.1 a ∉ U := by
  by_contra! h
  have hinj : Set.InjOn M.1 (↑Uᶜ : Set α) := M.1.injective.injOn
  have hmaps : ∀ a ∈ Uᶜ, M.1 a ∈ U := by simpa using h
  have hc := Finset.card_le_card_of_injOn M.1 hmaps hinj
  rw [Finset.card_compl] at hc
  have hu := Finset.card_le_univ U
  omega

lemma no_sign_on_complement [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = -f) : f = 0 := by
  ext M
  obtain ⟨a, ha, hma⟩ := exists_internal_edge_compl M U hU
  have he := congrFun (hf a ha (M.1 a) hma (M.partner_ne a).symm) M
  simp only [act_apply, Equiv.swap_inv, relabel_swap_partner, Pi.neg_apply] at he
  dsimp
  linarith

lemma mem_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    a ∈ closure M U ↔ a ∈ U ∨ M.1 a ∈ U := by
  simp only [closure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hb)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨M.1 a, h, M.partner_partner a⟩

lemma stable_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    M.1 a ∈ closure M U ↔ a ∈ closure M U := by
  simp only [mem_closure, partner_partner, or_comm]

lemma agree_on_closure [DecidableEq α] (U : Finset α) (M N : Pairing α)
    (h : ∀ a ∈ U, M.1 a = N.1 a) :
    ∀ a ∈ closure N U, M.1 a = N.1 a := by
  intro a ha
  rcases (mem_closure N U a).mp ha with ha | ha
  · exact h a ha
  · apply (M.partner_eq_iff a (N.1 a)).mpr
    rw [h _ ha, partner_partner]

lemma align_remaining [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α)
    (hMN : ∀ a ∈ U, M.1 a = N.1 a) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  classical
  let S := (closure N U)ᶜ
  have hagree := agree_on_closure U M N hMN
  have hcM : ∀ a ∈ closure N U, M.1 a ∈ closure N U := by
    intro a ha
    rw [hagree a ha]
    exact (stable_closure N U a).mpr ha
  have hcMi (a : α) : M.1 a ∈ closure N U ↔ a ∈ closure N U := by
    constructor
    · intro ha
      simpa using hcM (M.1 a) ha
    · exact hcM a
  have hM (a : α) : M.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, hcMi]
  have hN (a : α) : N.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, stable_closure]
  obtain ⟨q, hq⟩ := exists_relabel (restrict M S hM) (restrict N S hN)
  let p := q.extendDomain (Equiv.refl S)
  have hpin (a : α) (ha : a ∈ S) : p a = (q ⟨a, ha⟩).1 := by
    simpa [p] using Equiv.Perm.extendDomain_apply_subtype q (Equiv.refl S) ha
  have hpout (a : α) (ha : a ∉ S) : p a = a := by
    exact Equiv.Perm.extendDomain_apply_not_subtype q (Equiv.refl S) ha
  have hinter (a : α) : p (M.1 a) = N.1 (p a) := by
    by_cases ha : a ∈ S
    · have hh := congrArg (fun P : Pairing S => (P.1 (q ⟨a, ha⟩)).1) hq
      rw [hpin _ ((hM a).mpr ha), hpin a ha]
      simpa [restrict] using hh
    · have hma : M.1 a ∉ S := by simpa only [hM] using ha
      rw [hpout _ hma, hpout _ ha]
      exact hagree a (by simpa only [S, Finset.mem_compl, not_not] using ha)
  refine ⟨p, ?_, ?_⟩
  · intro a ha
    apply hpout
    simp only [S, Finset.mem_compl, not_not]
    exact (mem_closure N U a).mpr (Or.inl ha)
  · ext a
    obtain ⟨b, rfl⟩ := p.surjective a
    simpa using hinter b

lemma exists_relabel_fixing [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  obtain ⟨p, hp, hpM⟩ := align_partners U M N hMN
  obtain ⟨q, hq, hqM⟩ := align_remaining U (relabel p M) N hpM
  refine ⟨q * p, ?_, ?_⟩
  · intro a ha
    simp only [Equiv.Perm.mul_apply, hp a ha, hq a ha]
  · rw [relabel_mul, hqM]

lemma extend_swap [DecidableEq α] (S : Finset α) (x y : S) :
    (Equiv.swap x y).extendDomain (Equiv.refl S) = Equiv.swap x.1 y.1 := by
  ext a
  by_cases ha : a ∈ S
  · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
    by_cases hx : a = x.1 <;> by_cases hy : a = y.1 <;>
      simp [Equiv.swap_apply_def, Subtype.ext_iff, hx, hy]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
    have hx : a ≠ x.1 := by rintro rfl; exact ha x.2
    have hy : a ≠ y.1 := by rintro rfl; exact ha y.2
    simp [Equiv.swap_apply_def, hx, hy]

lemma invariant_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (p : Equiv.Perm α) (hp : ∀ a ∈ U, p a = a) : act p f = f := by
  classical
  let S := Uᶜ
  have hU (a : α) : p a ∈ U ↔ a ∈ U := by
    constructor
    · intro h
      have he : p a = a := p.injective (hp (p a) h)
      simpa [he] using h
    · intro h; simpa [hp a h] using h
  have hS (a : α) : p a ∈ S ↔ a ∈ S := by simp only [S, Finset.mem_compl, hU]
  have hind (q : Equiv.Perm S) : act (q.extendDomain (Equiv.refl S)) f = f := by
    induction q using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul q x y hxy ih =>
      rw [← Equiv.Perm.extendDomain_mul, act_mul, ih, extend_swap]
      apply hf x.1 (by simpa only [S, Finset.mem_compl] using x.2)
        y.1 (by simpa only [S, Finset.mem_compl] using y.2)
      exact fun h => hxy (Subtype.ext h)
  have he : (p.subtypePerm hS).extendDomain (Equiv.refl S) = p := by
    ext a
    by_cases ha : a ∈ S
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
      rfl
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
      exact (hp a (by simpa only [S, Finset.mem_compl, not_not] using ha)).symm
  rw [← he]
  exact hind _

lemma sameInternal_value_of_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (M N : Pairing α) (hMN : SameInternal U M N) : f M = f N := by
  obtain ⟨p, hp, hpM⟩ := exists_relabel_fixing U M N hMN
  have he := congrFun (invariant_of_swap_invariant U f hf p hp) N
  rw [act_apply, ← hpM, ← relabel_mul, inv_mul_cancel, relabel_one] at he
  simpa only [hpM] using he

lemma internalPattern_eq_iff [DecidableEq α] (U : Finset α) (M N : Pairing α) :
    internalPattern U M = internalPattern U N ↔ SameInternal U M N := by
  constructor
  · intro h a ha b hb
    have he := Finset.ext_iff.mp h (a,b)
    simpa [internalPattern, ha, hb] using he
  · intro h
    ext ⟨a,b⟩
    simp only [internalPattern, Finset.mem_filter, Finset.mem_product]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp_all [SameInternal]

lemma internal_indicator_mem_lowDegree [Fintype α] [DecidableEq α]
    (U : Finset α) (M : Pairing α) :
    (fun N => if internalPattern U N = internalPattern U M then (1 : ℝ) else 0)
      ∈ lowDegree edgeCoord (U.card * U.card) := by
  classical
  have h := boolean_pattern_mem_lowDegree edgeCoord (U ×ˢ U) (internalPattern U M)
  rw [Finset.card_product] at h
  convert h using 1
  ext N
  rw [Finset.prod_apply]
  have hf (e : α × α) (he : e ∈ U ×ˢ U) :
      (if e ∈ internalPattern U M then edgeCoord e else 1 - edgeCoord e) N =
        (if (N.1 e.1 = e.2 ↔ M.1 e.1 = e.2) then (1 : ℝ) else 0) := by
    by_cases hm : M.1 e.1 = e.2 <;> by_cases hn : N.1 e.1 = e.2 <;>
      simp [internalPattern, he, hm, hn, edgeCoord]
  rw [Finset.prod_congr rfl hf, Finset.prod_boole]
  congr 1
  rw [internalPattern_eq_iff]
  simp only [SameInternal, Finset.mem_product, Prod.forall]
  aesop

lemma mem_lowDegree_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f) :
    f ∈ lowDegree edgeCoord (U.card * U.card) := by
  apply mem_of_fiber_indicators (internalPattern U) f
  · intro M N hMN
    exact sameInternal_value_of_invariant U f hf M N
      ((internalPattern_eq_iff U M N).mp hMN)
  · exact internal_indicator_mem_lowDegree U

lemma act_swap_involution [DecidableEq α] (a b : α) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act (Equiv.swap a b) f) = f := by
  rw [← act_mul, Equiv.swap_mul_self, act_one]

lemma act_swap_conj [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (f : Pairing α → ℝ) :
    act (Equiv.swap (p a) (p b)) (act p f) = act p (act (Equiv.swap a b) f) := by
  rw [← act_mul, ← act_mul, Equiv.mul_swap_eq_swap_mul]

end Pairing
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.RepresentationDimension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

variable {h : ℕ}

lemma card_firstVertices {t : ℕ} (ht : t ≤ h) :
    (firstVertices h t).card = 2 * t := by
  simp [firstVertices, Fin.card_filter_val_lt, min_eq_right ht, Nat.mul_comm]

lemma pairSwap_commute (i j : Fin h) : Commute (pairSwap i) (pairSwap j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · change Equiv.swap (i,false) (i,true) * Equiv.swap (j,false) (j,true) =
      Equiv.swap (j,false) (j,true) * Equiv.swap (i,false) (i,true)
    rw [Equiv.mul_swap_eq_swap_mul]
    simp [Equiv.swap_apply_def, Ne.symm hij]

lemma act_pairSwap_commute (i j : Fin h) :
    Commute (Pairing.act (pairSwap i)).toLinearMap (Pairing.act (pairSwap j)).toLinearMap := by
  apply LinearMap.ext
  intro f
  change Pairing.act (pairSwap i) (Pairing.act (pairSwap j) f) = _
  rw [← Pairing.act_mul, (pairSwap_commute i j).eq, Pairing.act_mul]
  rfl

lemma exists_negative_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : f ∉ lowDegree Pairing.edgeCoord (U.card * U.card)) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (-1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.mem_lowDegree_of_swap_invariant U f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  have hz : f - Pairing.act (Equiv.swap a b) f = 0 := by
    simpa only [neg_smul, one_smul, sub_eq_add_neg] using he
  exact (sub_eq_zero.mp hz).symm

lemma exists_positive_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ) (hf : f ≠ 0) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.no_sign_on_complement U hU f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  exact eq_neg_of_add_eq_zero_left (by simpa only [one_smul, add_comm] using he)

lemma prescribed_sign_vector (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) :
    ∃ f ∈ W, f ≠ 0 ∧ ∀ i : Fin h, i.val < 2 * k →
      Pairing.act (pairSwap i) f = (if i.val < k then (-1 : ℝ) else 1) • f := by
  let χ (i : Fin h) : ℝ := if i.val < k then -1 else 1
  have hind : ∀ t : ℕ, t ≤ 2 * k → ∃ f ∈ W, f ≠ 0 ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨f, hf, hf0⟩ := hne
      exact ⟨f, hf, hf0, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨f, hf, hf0, he⟩ := ih (by omega)
      have hth : t < h := by omega
      let c : ℝ := if t < k then -1 else 1
      have hc : c = 1 ∨ c = -1 := by dsimp [c]; split_ifs <;> simp
      have hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
          f + c • Pairing.act (Equiv.swap a b) f ≠ 0 := by
        by_cases htk : t < k
        · dsimp [c]; rw [ite_eq_left htk]
          apply exists_negative_projection
          intro hlow
          have hd : (firstVertices h t).card * (firstVertices h t).card ≤ (4*k) * (4*k) := by
            rw [card_firstVertices hth.le]
            apply Nat.mul_self_le_mul_self
            omega
          exact hf0 ((Submodule.disjoint_def.mp hdis) f hf (lowDegree_mono _ hd hlow))
        · dsimp [c]; rw [ite_eq_right htk]
          apply exists_positive_projection _ _ f hf0
          rw [card_firstVertices hth.le]
          simp only [Vertices, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          omega
      obtain ⟨g, hg, hg0, hnew, hold⟩ := next_prescribed_sign W hW hth χ c hc f hf he hex
      refine ⟨g, hg, hg0, ?_⟩
      intro i hi
      by_cases hit : i.val < t
      · exact hold i hit
      · have hie : i = ⟨t, hth⟩ := Fin.ext (by change i.val = t; omega)
        subst i
        exact hnew
  exact hind (2*k) le_rfl

lemma choose_le_choose_of_le_of_le_compl {n k w : ℕ}
    (hkw : k ≤ w) (hw : w ≤ n - k) : n.choose k ≤ n.choose w := by
  have hmon : ∀ a b : ℕ, a ≤ b → b ≤ n / 2 → n.choose a ≤ n.choose b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; rfl
    | succ b hab ih =>
      intro hb
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hhalf : w ≤ n / 2
  · exact hmon k w hkw hhalf
  · have hwn : w ≤ n := hw.trans (Nat.sub_le _ _)
    rw [← Nat.choose_symm hwn]
    apply hmon k (n-w) <;> omega

lemma invariant_high_degree_dimension (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by
  classical
  obtain ⟨v, hv, hv0, he⟩ := prescribed_sign_vector k hk W hW hdis hne
  let A (i : Fin h) := (Pairing.act (pairSwap i)).toLinearMap
  let s₀ := Finset.univ.filter fun i : Fin h => i.val < 2*k
  obtain ⟨ψ, w, hw, hw0, hew, hp⟩ := simultaneous_sign_eigenvector_preserving A
    act_pairSwap_commute (fun i => Pairing.act_swap_involution (i,false) (i,true))
    W (fun i => hW (pairSwap i)) s₀ (fun i => if i.val < k then -1 else 1)
    v hv hv0 (by simpa [A, s₀] using he)
  have hpres (i : Fin h) (hi : i.val < 2*k) : ψ i = if i.val < k then -1 else 1 :=
    hp i (by simpa only [s₀, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
  let s := Finset.univ.filter fun i => ψ i = -1
  have hlow : k ≤ s.card := by
    let e (i : Fin k) : s := ⟨⟨i.val, by omega⟩, by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega)]
      exact ite_eq_left i.isLt⟩
    have hinj : Function.Injective e := by
      intro i j hij
      exact Fin.ext (congrArg (fun x : s => x.1.val) hij)
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hhigh : k ≤ sᶜ.card := by
    let e (i : Fin k) : ↥(sᶜ) := ⟨⟨k+i.val, by omega⟩, by
      simp only [Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega), ite_eq_right (by dsimp; omega)]
      norm_num⟩
    have hinj : Function.Injective e := by
      intro i j hij
      have heq := congrArg (fun x : ↥(sᶜ) => x.1.val) hij
      apply Fin.ext
      dsimp [e] at heq
      omega
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hsc : s.card ≤ h := Finset.card_le_univ s |>.trans_eq (Fintype.card_fin h)
  rw [Finset.card_compl, Fintype.card_fin] at hhigh
  have hchoose := choose_le_choose_of_le_of_le_compl hlow (by omega : s.card ≤ h-k)
  apply hchoose.trans
  let P (p : Equiv.Perm (Fin h)) := Pairing.act (Equiv.prodCongr p (Equiv.refl Bool))
  have hconj (p : Equiv.Perm (Fin h)) (i : Fin h) (f : Pairing (Vertices h) → ℝ) :
      A (p i) (P p f) = P p (A i f) :=
    Pairing.act_swap_conj (Equiv.prodCongr p (Equiv.refl Bool)) (i,false) (i,true) f
  have hsigne (i : Fin h) : A i w = (if i ∈ s then (-1 : ℝ) else 1) • w := by
    have hi := hew i
    rw [hi.2]
    congr 1
    by_cases his : ψ i = -1
    · simp [s, his]
    · have hie : ψ i = 1 := hi.1.resolve_right his
      simp [s, hie]
  simpa only [Fintype.card_fin] using
    binomial_le_finrank_of_eigenvector_mem A act_pairSwap_commute P hconj W
      (fun p => hW _) s w hw hw0 hsigne

end StandardPairs
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.invariant_high_degree_dimension := @_root_.OAI.MatchingSmoothing.invariant_high_degree_dimension
