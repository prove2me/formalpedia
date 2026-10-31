-- Prove2me | solution 1 for OAI.CycleClique.thm_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:08:41.584255+00:00
-- url     : https://prove2.me/submissions/7fa5e217-b701-4530-8bee-4a3af15aed5f

import Mathlib
import Definitions.Def_CycleCliqueRamsey
import Definitions.Def_OAIQ107D061
import Definitions.Def_OAIQ107D125
import Definitions.Def_OAIQ107D127
import Theorems.Thm_OAI_CycleClique_finite_range_verified

section
-- module Solutions.OAIQ107_CC.Compat
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ColouredPaths
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exists_common_neighbor_different_colours {V : Type*} {H : SimpleGraph V}
    (hconn : H.Connected) (hnb : ¬ H.IsBipartite) (χ : V → Fin 2)
    (hnc : ∃ y z, χ y ≠ χ z) :
    ∃ x y z, H.Adj x y ∧ H.Adj x z ∧ χ y ≠ χ z := by
  classical
  by_contra h
  push Not at h
  have hcol : ¬ (∀ ⦃v w⦄, H.Adj v w → χ v ≠ χ w) := by
    intro hc
    exact hnb ⟨SimpleGraph.Coloring.mk χ (fun {v w} hvw => hc hvw)⟩
  push Not at hcol
  obtain ⟨a, b, hab, heq⟩ := hcol
  have propagate : ∀ {u v : V} (p : H.Walk u v),
      ∀ z, H.Adj u z → χ u = χ z → χ v = χ u := by
    intro u v p
    induction p with
    | nil => simp
    | @cons u w v huw p ih =>
      intro z huz heq
      have hwu : χ w = χ u := (h u z w huz huw).symm.trans heq.symm
      exact (ih u huw.symm hwu).trans hwu
  obtain ⟨y, z, hyz⟩ := hnc
  have hy : χ y = χ a := by
    obtain ⟨p⟩ := hconn.preconnected a y
    exact propagate p b hab heq
  have hz : χ z = χ a := by
    obtain ⟨p⟩ := hconn.preconnected a z
    exact propagate p b hab heq
  exact hyz (hy.trans hz.symm)

 
theorem exists_longest_path_from {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    ∃ (v : V) (p : G.Walk x v), p.IsPath ∧
      ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length := by
  let S := {n : ℕ | ∃ (v : V) (p : G.Walk x v), p.IsPath ∧ p.length = n}
  have hS : S.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro n ⟨v, p, hp, rfl⟩
    exact hp.length_lt.le)
  obtain ⟨n, ⟨⟨v, p, hp, hn⟩, hmax⟩⟩ :=
    hS.exists_maximal ⟨0, ⟨x, .nil, by simp⟩⟩
  refine ⟨v, p, hp, fun w q hq => ?_⟩
  have := hmax (show q.length ∈ S from ⟨w, q, hq, rfl⟩)
  omega

 
theorem longest_path_endpoint_neighbors {V : Type*} {G : SimpleGraph V}
    {x v : V} (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length) :
    ∀ w, G.Adj v w → w ∈ p.support := by
  intro w hvw
  by_contra hw
  have := hmax w (p.concat hvw) (hp.concat hw hvw)
  simp only [SimpleGraph.Walk.length_concat] at this
  omega

 

theorem different_colour_prefix {V : Type*} {G : SimpleGraph V}
    {x b y z : V} (χ : V → Fin 2) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : χ y ≠ χ z) (p : G.Walk x b) (hp : p.IsPath)
    (hy : y ∉ p.support) (hz : z ∉ p.support)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hlen : ℓ ≤ p.length + 1) :
    ∃ a b, χ a ≠ χ b ∧ ∃ q : G.Walk a b, q.IsPath ∧ q.length = ℓ := by
  let q := p.take (ℓ - 1)
  have hq : q.IsPath := hp.take _
  have hsub : ∀ v, v ∈ q.support → v ∈ p.support := by
    intro v hv
    rw [SimpleGraph.Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  have hqlen : q.length = ℓ - 1 := by
    simp only [q, SimpleGraph.Walk.take_length]
    omega
  by_cases hcy : χ y = χ (p.getVert (ℓ - 1))
  · refine ⟨z, _, ?_, .cons hxz.symm q, ?_, ?_⟩
    · exact fun hcz => hyz (hcy.trans hcz.symm)
    · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq, fun h => hz (hsub _ h)⟩
    · simp only [SimpleGraph.Walk.length_cons, hqlen]
      omega
  · refine ⟨y, _, hcy, .cons hxy.symm q, ?_, ?_⟩
    · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq, fun h => hy (hsub _ h)⟩
    · simp only [SimpleGraph.Walk.length_cons, hqlen]
      omega

 
theorem path_rotation_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath) (i : ℕ) (hi : i < p.length)
    (hiv : G.Adj (p.getVert i) v) :
    ∃ q : G.Walk x (p.getVert (i + 1)), q.IsPath ∧ q.support.Perm p.support ∧
      ∀ j, j ≤ i → q.getVert j = p.getVert j := by
  let q := (p.take i).append (.cons hiv (p.drop (i + 1)).reverse)
  have hsupport : q.support =
      p.support.take (i + 1) ++ (p.support.drop (i + 1)).reverse := by
    simp only [q, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      List.tail_cons, SimpleGraph.Walk.support_take, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.drop_support_eq_support_drop_min, Nat.min_eq_left (by omega :
        i + 1 ≤ p.length)]
  have hperm : q.support.Perm p.support := by
    rw [hsupport]
    simpa only [List.take_append_drop] using
      (List.reverse_perm (p.support.drop (i + 1))).append_left (p.support.take (i + 1))
  refine ⟨q, (q.isPath_def).mpr (hperm.nodup_iff.mpr hp.support_nodup), hperm, ?_⟩
  intro j hj
  simp only [q, SimpleGraph.Walk.getVert_append', SimpleGraph.Walk.take_length,
    Nat.min_eq_left hi.le, ite_eq_left hj, SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right hj]

theorem path_rotation {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath) (i : ℕ) (hi : i < p.length)
    (hiv : G.Adj (p.getVert i) v) :
    ∃ q : G.Walk x (p.getVert (i + 1)), q.IsPath ∧ q.support.Perm p.support := by
  obtain ⟨q, hq, hperm, _⟩ := path_rotation_prefix p hp i hi hiv
  exact ⟨q, hq, hperm⟩


theorem mem_pathEnds_support {V : Type*} {G : SimpleGraph V} {x v : V} {W : List V}
    (hv : v ∈ pathEnds G x W) : v ∈ W := by
  obtain ⟨p, _, hperm⟩ := hv
  exact hperm.mem_iff.mp p.end_mem_support

theorem pathEnds_no_start {V : Type*} {G : SimpleGraph V} {x : V} {W : List V}
    (hW : 1 < W.length) : x ∉ pathEnds G x W := by
  rintro ⟨p, hp, hperm⟩
  have hp0 := (SimpleGraph.Walk.isPath_iff_nil.mp hp).length_eq_zero
  have hlen := hperm.length_eq
  rw [SimpleGraph.Walk.length_support] at hlen
  omega

 
theorem successor_mem_pathEnds {V : Type*} {G : SimpleGraph V} {x e : V}
    {W : List V} (p : G.Walk x e) (hp : p.IsPath) (hperm : p.support.Perm W)
    (i : ℕ) (hi : i < p.length) (hie : G.Adj (p.getVert i) e) :
    p.getVert (i + 1) ∈ pathEnds G x W := by
  obtain ⟨q, hq, hqp⟩ := path_rotation p hp i hi hie
  exact ⟨q, hq, hqp.trans hperm⟩

 

theorem degree_le_card_pathEnds {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x e : V} {W : List V}
    (p : G.Walk x e) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hnb : ∀ v, G.Adj e v → v ∈ p.support) :
    G.degree e ≤ (pathEnds G x W).ncard := by
  classical
  have hidx : ∀ v : G.neighborSet e,
      ∃ n, n < p.length ∧ p.getVert n = v.val := by
    intro v
    obtain ⟨n, hn, hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
      (hnb v.val v.property)
    refine ⟨n, lt_of_le_of_ne hle ?_, hn⟩
    intro heq
    subst n
    have : e = v.val := by simpa using hn
    exact G.ne_of_adj v.property this
  choose idx hi heq using hidx
  let f : G.neighborSet e → pathEnds G x W := fun v =>
    ⟨p.getVert (idx v + 1), successor_mem_pathEnds p hp hperm (idx v) (hi v)
      (by rw [heq]; exact v.property.symm)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hget : p.getVert (idx a + 1) = p.getVert (idx b + 1) := congrArg Subtype.val hab
    have hia := hi a
    have hib := hi b
    have hindex := hp.getVert_injOn (by dsimp; omega) (by dsimp; omega) hget
    have : idx a = idx b := by omega
    apply Subtype.ext
    rw [← heq a, ← heq b, this]
  have hcard := Fintype.card_le_of_injective f hf
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact hcard

 
theorem pathEnds_neighbors {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    {e : V} (he : e ∈ pathEnds G x p.support) :
    ∀ w, G.Adj e w → w ∈ p.support := by
  obtain ⟨q, hq, hqp⟩ := he
  have hlen : q.length = p.length := by
    have := hqp.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  intro w hew
  apply hqp.mem_iff.mp
  exact longest_path_endpoint_neighbors q hq (by simpa only [hlen] using hmax) w hew

 
theorem pathEnds_isClique {V : Type*} [Fintype V] {G : SimpleGraph V}
    {x v : V} (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hexpand : ∀ a ∈ pathEnds G x p.support, ∀ b ∈ pathEnds G x p.support,
      a ≠ b → ¬ G.Adj a b →
      p.length + 2 ≤ (closedNeighborhood G {a, b}).ncard) :
    G.IsClique (pathEnds G x p.support) := by
  classical
  intro a ha b hb hab
  by_contra hnab
  have hsub : closedNeighborhood G {a, b} ⊆ (p.support.toFinset : Set V) := by
    intro w hw
    rcases hw with hw | ⟨u, hu, huw⟩
    · rcases hw with rfl | hw
      · simpa using mem_pathEnds_support ha
      · have : w = b := by simpa using hw
        subst w
        simpa using mem_pathEnds_support hb
    · rcases hu with rfl | hu
      · simpa using pathEnds_neighbors p hmax ha w huw
      · have : u = b := by simpa using hu
        subst u
        simpa using pathEnds_neighbors p hmax hb w huw
  have hle := Set.ncard_le_ncard hsub
  have hcard : (p.support.toFinset : Set V).ncard = p.length + 1 := by
    simp only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support]
  have := hexpand a ha b hb hab hnab
  omega

 
theorem pathEnds_successor_closed {V : Type*} {G : SimpleGraph V} {x v : V}
    {W : List V} (p : G.Walk x v) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hclique : G.IsClique (pathEnds G x W))
    (i : ℕ) (hi : i < p.length) (hEi : p.getVert i ∈ pathEnds G x W) :
    p.getVert (i + 1) ∈ pathEnds G x W := by
  apply successor_mem_pathEnds p hp hperm i hi
  apply hclique hEi (show v ∈ pathEnds G x W from ⟨p, hp, hperm⟩)
  intro heq
  have := (hp.getVert_eq_end_iff hi.le).mp heq
  omega

 
theorem pathEnds_final_segment {V : Type*} {G : SimpleGraph V} {x v : V}
    {W : List V} (p : G.Walk x v) (hp : p.IsPath) (hperm : p.support.Perm W)
    (hclique : G.IsClique (pathEnds G x W)) (hW : 1 < W.length) :
    ∃ k, 0 < k ∧ k ≤ p.length ∧ ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x W ↔ k ≤ i) := by
  classical
  have hex : ∃ i, i ≤ p.length ∧ p.getVert i ∈ pathEnds G x W := by
    refine ⟨p.length, le_rfl, ?_⟩
    simpa using (show v ∈ pathEnds G x W from ⟨p, hp, hperm⟩)
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hx : x ∈ pathEnds G x W := by simpa only [← show k = Nat.find hex from rfl,
      hk0, SimpleGraph.Walk.getVert_zero] using hk.2
    exact pathEnds_no_start hW hx
  refine ⟨k, hkpos, hk.1, fun i hi => ⟨?_, ?_⟩⟩
  · intro hEi
    exact Nat.find_min' hex ⟨hi, hEi⟩
  · intro hki
    induction i, hki using Nat.le_induction with
    | base => exact hk.2
    | succ i hki ih =>
      exact pathEnds_successor_closed p hp hperm hclique i (by omega) (ih (by omega))

 

theorem pathEnd_ordering_preserving_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (_ : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (hw : w ∈ pathEnds G x p.support) (hw0 : w ≠ p.getVert k) :
    ∃ q : G.Walk x w, q.IsPath ∧ q.support.Perm p.support ∧
      ∀ j, j ≤ k → q.getVert j = p.getVert j := by
  obtain ⟨i, hiw, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (mem_pathEnds_support hw)
  have hki : k < i := by
    have := (hsegment i hi).mp (hiw ▸ hw)
    by_contra hn
    have : k = i := by omega
    exact hw0 (hiw.symm.trans (congrArg p.getVert this.symm))
  have hpred : p.getVert (i - 1) ∈ pathEnds G x p.support :=
    (hsegment _ (by omega)).mpr (by omega)
  have hadj : G.Adj (p.getVert (i - 1)) v := by
    apply hclique hpred (show v ∈ pathEnds G x p.support from ⟨p, hp, .refl _⟩)
    intro heq
    have := (hp.getVert_eq_end_iff (by omega)).mp heq
    omega
  have hrot := path_rotation_prefix p hp (i - 1) (by omega) hadj
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i), hiw] at hrot
  obtain ⟨q, hq, hperm, hpre⟩ := hrot
  exact ⟨q, hq, hperm, fun j hj => hpre j (by omega)⟩

 
theorem pathEnd_attachment_of_common_prefix {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (q : G.Walk x w) (hq : q.IsPath) (hperm : q.support.Perm p.support)
    (hpre : ∀ j, j < k → q.getVert j = p.getVert j) :
    ∀ a, G.Adj w a → a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  have hlen : q.length = p.length := by
    have := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  intro a ha
  by_cases haE : a ∈ pathEnds G x p.support
  · exact Or.inl haE
  right
  obtain ⟨j, hja, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (pathEnds_neighbors p hmax ⟨q, hq, hperm⟩ a ha)
  have hjk : j < k := by
    by_contra hn
    exact haE (hja ▸ (hsegment j hj).mpr (by omega))
  have hjprec : j = k - 1 := by
    by_contra hn
    have hsucc : j + 1 < k := by omega
    have hadj : G.Adj (q.getVert j) w := by rw [hpre j hjk, hja]; exact ha.symm
    have he := successor_mem_pathEnds q hq hperm j (by omega) hadj
    rw [hpre (j + 1) hsucc] at he
    have := (hsegment (j + 1) (by omega)).mp he
    omega
  exact hja.symm.trans (congrArg p.getVert hjprec)

 
theorem pathEnds_partial_attachment {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w : V} (hw : w ∈ pathEnds G x p.support) (hw0 : w ≠ p.getVert k) :
    ∀ a, G.Adj w a → a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  obtain ⟨q, hq, hperm, hpre⟩ := pathEnd_ordering_preserving_prefix p hp hclique hk
    hsegment hw hw0
  exact pathEnd_attachment_of_common_prefix p hmax hkpos hk hsegment q hq hperm
    (fun j hj => hpre j hj.le)

 

theorem pathEnds_attachment_of_two_entries {V : Type*} {G : SimpleGraph V} {x v : V}
    (p : G.Walk x v) (hp : p.IsPath)
    (hmax : ∀ (w : V) (q : G.Walk x w), q.IsPath → q.length ≤ p.length)
    (hclique : G.IsClique (pathEnds G x p.support))
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ p.length)
    (hsegment : ∀ i, i ≤ p.length →
      (p.getVert i ∈ pathEnds G x p.support ↔ k ≤ i))
    {w₁ : V} (hw₁ : w₁ ∈ pathEnds G x p.support) (hne : w₁ ≠ p.getVert k)
    (hentry : G.Adj (p.getVert (k - 1)) w₁) :
    ∀ w ∈ pathEnds G x p.support, ∀ a, G.Adj w a →
      a ∈ pathEnds G x p.support ∨ a = p.getVert (k - 1) := by
  intro w hw
  by_cases hww0 : w = p.getVert k
  · subst w
    obtain ⟨q, hq, hperm, hpre⟩ := pathEnd_ordering_preserving_prefix p hp hclique hk
      hsegment hw₁ hne
    have hlen : q.length = p.length := by
      have := hperm.length_eq
      simp only [SimpleGraph.Walk.length_support] at this
      omega
    have hadj : G.Adj (q.getVert (k - 1)) w₁ := by
      rw [hpre _ (by omega)]
      exact hentry
    have hrot := path_rotation_prefix q hq (k - 1) (by omega) hadj
    rw [Nat.sub_add_cancel hkpos, hpre k le_rfl] at hrot
    obtain ⟨r, hr, hrperm, hrpre⟩ := hrot
    exact pathEnd_attachment_of_common_prefix p hmax hkpos hk hsegment r hr
      (hrperm.trans hperm) (fun j hj => (hrpre j (by omega)).trans (hpre j (by omega)))
  · exact pathEnds_partial_attachment p hp hmax hclique hkpos hk hsegment hw hww0



theorem within_le {V : Type*} (G : SimpleGraph V) (S : Set V) : within G S ≤ G :=
  fun _ _ h => h.1

theorem within_support {V : Type*} {G : SimpleGraph V} {S : Set V} {x v : V}
    (p : (within G S).Walk x v) (hx : x ∈ S) : ∀ w ∈ p.support, w ∈ S := by
  induction p with
  | nil => simpa using hx
  | @cons u v w huv p ih =>
    intro a ha
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact huv.2.1
    · exact ih huv.2.2 a ha


theorem deleted_component {V : Type*} {H : SimpleGraph V} {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) :
    ∃ S : Set V, x ∈ S ∧ y ∉ S ∧ z ∉ S ∧
      (∀ a ∈ S, ∀ b ∈ S, (within H S).Reachable a b) ∧
      (∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) := by
  let D := within H {v | v ≠ y ∧ v ≠ z}
  let S := {v | D.Reachable x v}
  have hx : x ∈ S := SimpleGraph.Reachable.rfl
  have havoid : ∀ v ∈ S, v ≠ y ∧ v ≠ z := by
    rintro v ⟨p⟩
    exact within_support p ⟨hxy, hxz⟩ v p.end_mem_support
  refine ⟨S, hx, fun hy => (havoid y hy).1 rfl, fun hz => (havoid z hz).2 rfl, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨p⟩ := (ha : D.Reachable x a).symm.trans hb
    have hS : ∀ w ∈ p.support, w ∈ S := by
      intro w hw
      obtain ⟨i, hi, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
      rw [← hi]
      exact (ha : D.Reachable x a).trans ⟨p.take i⟩
    exact ⟨walkWithin (p.mapLe (within_le H _)) (by simpa using hS)⟩
  · intro a ha b hab
    by_cases hby : b = y
    · exact Or.inr (Or.inl hby)
    by_cases hbz : b = z
    · exact Or.inr (Or.inr hbz)
    exact Or.inl ((ha : D.Reachable x a).trans (SimpleGraph.Adj.reachable
      (show D.Adj a b from ⟨hab, havoid a ha, hby, hbz⟩)))

theorem ncard_neighborSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

 
theorem degree_add_one_le_of_neighbors_subset {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Set V}
    (hv : v ∈ S) (hS : ∀ w, G.Adj v w → w ∈ S) : G.degree v + 1 ≤ S.ncard := by
  have hsub : insert v (G.neighborSet v) ⊆ S := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact hS w hw
  have hc := Set.ncard_le_ncard hsub
  simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
    ncard_neighborSet] using hc

 
theorem adj_of_neighbors_subset_of_card {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {S : Set V}
    (hv : v ∈ S) (hS : ∀ w, G.Adj v w → w ∈ S)
    (hcard : S.ncard ≤ G.degree v + 1) : ∀ w ∈ S, w ≠ v → G.Adj v w := by
  classical
  have hsub : insert v (G.neighborSet v) ⊆ S := by
    intro w hw
    rcases hw with rfl | hw
    · exact hv
    · exact hS w hw
  have heq : insert v (G.neighborSet v) = S := by
    apply Set.eq_of_subset_of_ncard_le hsub
    simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
      ncard_neighborSet] using hcard
  intro w hw hne
  rw [← heq] at hw
  exact hw.resolve_left hne

 
theorem clique_ncard_lt {V : Type*} [Fintype V] {H : SimpleGraph V} {s : ℕ}
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) {E : Set V} (hE : H.IsClique E) :
    E.ncard < s := by
  classical
  have hf : H.CliqueFree s := by
    by_contra hn
    exact hfree ((SimpleGraph.not_cliqueFree_iff_top_isContained s).mp hn)
  by_contra hn
  have hle : s ≤ E.toFinset.card := by simpa only [← Set.ncard_eq_toFinset_card'] using
    (Nat.le_of_not_gt hn)
  apply hf.mono hle E.toFinset
  exact ⟨by simpa using hE, rfl⟩

 
theorem degree_le_add_two_of_boundary {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj] {v y z : V}
    (hb : ∀ w, H.Adj v w → K.Adj v w ∨ w = y ∨ w = z) :
    H.degree v ≤ K.degree v + 2 := by
  have hsub : H.neighborSet v ⊆ insert y (insert z (K.neighborSet v)) := by
    intro w hw
    rcases hb w hw with hw | hw | hw
    · exact Or.inr (Or.inr hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  have hle := Set.ncard_le_ncard hsub
  have hy := Set.ncard_insert_le y (insert z (K.neighborSet v))
  have hz := Set.ncard_insert_le z (K.neighborSet v)
  rw [ncard_neighborSet] at hle hz
  omega

 
theorem exists_mem_ne_of_ncard {V : Type*} [Finite V] {E : Set V} {w₀ : V}
    (hcard : 2 ≤ E.ncard) : ∃ w ∈ E, w ≠ w₀ := by
  by_contra hn
  push Not at hn
  have hsub : E ⊆ {w₀} := fun w hw => hn w hw
  have hle := Set.ncard_le_ncard hsub
  simp only [Set.ncard_singleton] at hle
  omega

 

theorem endpoint_clique_two_entries {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    {s : ℕ} (hs : 4 ≤ s) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ w, s ≤ H.degree w)
    {E : Set V} (hE : H.IsClique E) (hsize : s - 2 ≤ E.ncard)
    {u w₀ y z : V} (hw₀ : w₀ ∈ E) (hu : u ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (huy : u ≠ y) (huz : u ≠ z)
    (hboundary : ∀ w ∈ E, ∀ a, H.Adj w a → K.Adj w a ∨ a = y ∨ a = z)
    (hpartial : ∀ w ∈ E, w ≠ w₀ → ∀ a, K.Adj w a → a ∈ E ∨ a = u)
    (henddegree : ∀ w ∈ E, K.degree w ≤ E.ncard) :
    ∃ w ∈ E, w ≠ w₀ ∧ K.Adj u w := by
  classical
  have hupper := clique_ncard_lt hfree hE
  have hcases : E.ncard = s - 2 ∨ E.ncard = s - 1 := by omega
  by_contra hno
  push Not at hno
  rcases hcases with hsmall | hlarge
  · obtain ⟨w, hw, hww₀⟩ := exists_mem_ne_of_ncard (show 2 ≤ E.ncard by omega)
    have hnb : ∀ a, H.Adj w a → a ∈ insert u (insert y (insert z E)) := by
      intro a ha
      rcases hboundary w hw a ha with ha | rfl | rfl
      · rcases hpartial w hw hww₀ a ha with ha | rfl
        · exact Or.inr (Or.inr (Or.inr ha))
        · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hcard : (insert u (insert y (insert z E))).ncard ≤ H.degree w + 1 := by
      have := Set.ncard_insert_le u (insert y (insert z E))
      have := Set.ncard_insert_le y (insert z E)
      have := Set.ncard_insert_le z E
      have := hdegree w
      omega
    have hwu : H.Adj w u := adj_of_neighbors_subset_of_card
      (by simp [hw]) hnb hcard u (by simp) (fun heq => hu (heq ▸ hw))
    rcases hboundary w hw u hwu with hwu | h | h
    · exact hno w hw hww₀ hwu.symm
    · exact huy h
    · exact huz h
  · have hboth : ∀ w ∈ E, w ≠ w₀ → H.Adj w y ∧ H.Adj w z := by
      intro w hw hww₀
      have hnb : ∀ a, H.Adj w a → a ∈ insert y (insert z E) := by
        intro a ha
        rcases hboundary w hw a ha with ha | rfl | rfl
        · rcases hpartial w hw hww₀ a ha with haE | rfl
          · exact Or.inr (Or.inr haE)
          · exact False.elim (hno w hw hww₀ ha.symm)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      have hcard : (insert y (insert z E)).ncard ≤ H.degree w + 1 := by
        have := Set.ncard_insert_le y (insert z E)
        have := Set.ncard_insert_le z E
        have := hdegree w
        omega
      have hall := adj_of_neighbors_subset_of_card (G := H) (v := w)
        (by simp [hw]) hnb hcard
      exact ⟨hall y (by simp) (fun heq => hy (heq ▸ hw)),
        hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
    have hw₀one : H.Adj w₀ y ∨ H.Adj w₀ z := by
      by_contra hn
      push Not at hn
      have hsub : H.neighborSet w₀ ⊆ K.neighborSet w₀ := by
        intro a ha
        rcases hboundary w₀ hw₀ a ha with haK | rfl | rfl
        · exact haK
        · exact False.elim (hn.1 ha)
        · exact False.elim (hn.2 ha)
      have hc := Set.ncard_le_ncard hsub
      rw [ncard_neighborSet, ncard_neighborSet] at hc
      have := henddegree w₀ hw₀
      have := hdegree w₀
      omega
    have hbad : ∀ t, t ∉ E → H.Adj w₀ t →
        (∀ w ∈ E, w ≠ w₀ → H.Adj w t) → False := by
      intro t ht hw₀t hall
      have hEt : H.IsClique (insert t E) := hE.insert (by
        intro w hw _
        by_cases heq : w = w₀
        · subst w; exact hw₀t.symm
        · exact (hall w hw heq).symm)
      have := clique_ncard_lt hfree hEt
      rw [Set.ncard_insert_of_notMem ht] at this
      omega
    rcases hw₀one with h | h
    · exact hbad y hy h (fun w hw hne => (hboth w hw hne).1)
    · exact hbad z hz h (fun w hw hne => (hboth w hw hne).2)

 
theorem endpoint_clique_common_neighbor {V : Type*} [Fintype V]
    {H K : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
    {s : ℕ} (hs : 4 ≤ s) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ w, s ≤ H.degree w)
    {E : Set V} (hE : H.IsClique E) (hsize : s - 2 ≤ E.ncard)
    {u y z : V} (hu : u ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hboundary : ∀ w ∈ E, ∀ a, H.Adj w a → K.Adj w a ∨ a = y ∨ a = z)
    (hattach : ∀ w ∈ E, ∀ a, K.Adj w a → a ∈ E ∨ a = u)
    (hKH : K ≤ H) : ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  have hupper := clique_ncard_lt hfree hE
  have hcases : E.ncard = s - 2 ∨ E.ncard = s - 1 := by omega
  rcases hcases with hsmall | hlarge
  · obtain ⟨w, hw, _⟩ := exists_mem_ne_of_ncard (w₀ := u) (show 2 ≤ E.ncard by omega)
    have hnb : ∀ a, H.Adj w a → a ∈ insert u (insert y (insert z E)) := by
      intro a ha
      rcases hboundary w hw a ha with ha | rfl | rfl
      · rcases hattach w hw a ha with ha | rfl
        · exact Or.inr (Or.inr (Or.inr ha))
        · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    have hcard : (insert u (insert y (insert z E))).ncard ≤ H.degree w + 1 := by
      have := Set.ncard_insert_le u (insert y (insert z E))
      have := Set.ncard_insert_le y (insert z E)
      have := Set.ncard_insert_le z E
      have := hdegree w
      omega
    have hall := adj_of_neighbors_subset_of_card (G := H) (v := w)
      (by simp [hw]) hnb hcard
    exact ⟨w, hw, hall y (by simp) (fun heq => hy (heq ▸ hw)),
      hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
  · by_contra hno
    push Not at hno
    have hallu : ∀ w ∈ E, H.Adj w u := by
      intro w hw
      by_contra hnwu
      have heither : ¬ H.Adj w y ∨ ¬ H.Adj w z := by tauto
      have hcount : ∀ t, (∀ a, H.Adj w a → a ∈ insert t E) → False := by
        intro t hnb
        have hbound := degree_add_one_le_of_neighbors_subset
          (G := H) (v := w) (by simp [hw]) hnb
        have := Set.ncard_insert_le t E
        have := hdegree w
        omega
      rcases heither with hny | hnz
      · apply hcount z
        intro a ha
        rcases hboundary w hw a ha with haK | rfl | rfl
        · rcases hattach w hw a haK with haE | rfl
          · exact Or.inr haE
          · exact False.elim (hnwu (hKH haK))
        · exact False.elim (hny ha)
        · exact Or.inl rfl
      · apply hcount y
        intro a ha
        rcases hboundary w hw a ha with haK | rfl | rfl
        · rcases hattach w hw a haK with haE | rfl
          · exact Or.inr haE
          · exact False.elim (hnwu (hKH haK))
        · exact Or.inl rfl
        · exact False.elim (hnz ha)
    have hEu : H.IsClique (insert u E) := hE.insert (fun w hw _ => (hallu w hw).symm)
    have := clique_ncard_lt hfree hEu
    rw [Set.ncard_insert_of_notMem hu] at this
    omega

 

theorem path_avoids_attached_set {V : Type*} {K : SimpleGraph V} {E : Set V} {u b : V}
    (p : K.Walk u b) (hp : p.IsPath) (hb : b ∉ E)
    (hattach : ∀ w ∈ E, ∀ a, K.Adj w a → a ∈ E ∨ a = u) :
    ∀ w ∈ p.support, w ∉ E := by
  intro w hw hwE
  obtain ⟨i, hi, hilen⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  have hiE : p.getVert i ∈ E := hi ▸ hwE
  obtain ⟨d, hd, hfst, hsnd⟩ := (p.drop i).exists_boundary_dart E hiE hb
  have hsndu : d.snd = u := (hattach d.fst hfst d.snd d.adj).resolve_left hsnd
  have hdp : d ∈ p.darts := by
    rw [SimpleGraph.Walk.darts_drop] at hd
    exact List.mem_of_mem_drop hd
  have humem : u ∈ p.support.tail := by
    rw [← SimpleGraph.Walk.map_snd_darts]
    exact List.mem_map.mpr ⟨d, hdp, hsndu⟩
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hnd
  exact hnd.1 humem

 
theorem reachable_after_removing_attached_set {V : Type*} {H : SimpleGraph V}
    {S E : Set V} {u b : V} (hu : u ∈ S \ E) (hb : b ∈ S \ E)
    (hconn : (within H S).Reachable u b)
    (hattach : ∀ w ∈ E, ∀ a, (within H S).Adj w a → a ∈ E ∨ a = u) :
    (within H (S \ E)).Reachable u b := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  have hS := within_support p hu.1
  have hE := path_avoids_attached_set p hp hb.2 hattach
  exact ⟨walkWithin (p.mapLe (within_le H S)) (by
    intro w hw
    have hw' : w ∈ p.support := by simpa using hw
    exact ⟨hS w hw', hE w hw'⟩)⟩

 
theorem deletion_component_card {V : Type*} [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {s : ℕ} (hs : 4 ≤ s)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) (hdegree : ∀ w, s ≤ H.degree w)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    {S : Set V} (hS : S.Nonempty) {y z : V} (hy : y ∉ S) (hz : z ∉ S)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) :
    2 * s - 2 ≤ S.ncard := by
  classical
  have hnotclique : ¬ H.IsClique S := by
    intro hcl
    have hsmall := clique_ncard_lt hfree hcl
    obtain ⟨v, hv⟩ := hS
    have hnb : ∀ w, H.Adj v w → w ∈ insert y (insert z S) := by
      intro w hw
      rcases hboundary v hv w hw with hw | rfl | rfl
      · exact Or.inr (Or.inr hw)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hc := degree_add_one_le_of_neighbors_subset (G := H) (v := v)
      (by simp [hv]) hnb
    have hc₁ := Set.ncard_insert_le y (insert z S)
    have hc₂ := Set.ncard_insert_le z S
    have hdegreev := hdegree v
    have hcard : S.ncard = s - 1 := by omega
    have hall : ∀ w ∈ S, H.Adj w y := by
      intro w hw
      have hnb' : ∀ a, H.Adj w a → a ∈ insert y (insert z S) := by
        intro a ha
        rcases hboundary w hw a ha with ha | rfl | rfl
        · exact Or.inr (Or.inr ha)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      apply adj_of_neighbors_subset_of_card (G := H) (v := w) (by simp [hw]) hnb'
      · have := hdegree w
        omega
      · simp
      · exact fun heq => hy (heq ▸ hw)
    have hcl' : H.IsClique (insert y S) := hcl.insert (fun w hw _ => (hall w hw).symm)
    have hbad := clique_ncard_lt hfree hcl'
    rw [Set.ncard_insert_of_notMem hy] at hbad
    omega
  change ¬ Set.Pairwise S H.Adj at hnotclique
  simp only [Set.Pairwise] at hnotclique
  push Not at hnotclique
  obtain ⟨a, ha, b, hb, hab, hnab⟩ := hnotclique
  have hsub : closedNeighborhood H {a, b} ⊆ insert y (insert z S) := by
    intro w hw
    rcases hw with hw | ⟨v, hv, hvw⟩
    · have hwS : w ∈ S := by
        rcases hw with rfl | hw
        · exact ha
        · have : w = b := by simpa using hw
          simpa only [this] using hb
      exact Or.inr (Or.inr hwS)
    · have hvS : v ∈ S := by
        rcases hv with rfl | hv
        · exact ha
        · have : v = b := by simpa using hv
          simpa only [this] using hb
      rcases hboundary v hvS w hvw with hw | rfl | rfl
      · exact Or.inr (Or.inr hw)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have hc := Set.ncard_le_ncard hsub
  have hc₁ := Set.ncard_insert_le y (insert z S)
  have hc₂ := Set.ncard_insert_le z S
  have he := hexpand a b hab hnab
  omega

 
theorem closedNeighborhood_within_boundary {V : Type*} {H : SimpleGraph V}
    {S I : Set V} {y z : V} (hI : I ⊆ S)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z) :
    closedNeighborhood H I ⊆ insert y (insert z (closedNeighborhood (within H S) I)) := by
  intro w hw
  rcases hw with hw | ⟨a, ha, haw⟩
  · exact Or.inr (Or.inr (Or.inl hw))
  · rcases hboundary a (hI ha) w haw with hwS | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, haw, hI ha, hwS⟩))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

 

theorem clique_path_between {V : Type*} [Fintype V] {G : SimpleGraph V}
    {E : Set V} (hE : G.IsClique E) {a b : V} (ha : a ∈ E) (hb : b ∈ E)
    (hab : a ≠ b) : ∃ p : G.Walk a b, p.IsPath ∧
      (∀ v, v ∈ p.support ↔ v ∈ E) ∧ p.length + 1 = E.ncard := by
  classical
  let T := (E.toFinset.erase a).erase b
  let L := a :: (T.toList ++ [b])
  have hmem : ∀ v, v ∈ L ↔ v ∈ E := by
    intro v
    simp only [L, List.mem_cons, List.mem_append, Finset.mem_toList,
      List.not_mem_nil, or_false, T, Finset.mem_erase, Set.mem_toFinset]
    constructor
    · rintro (rfl | ⟨_, _, hv⟩ | rfl)
      · exact ha
      · exact hv
      · exact hb
    · intro hv
      by_cases hva : v = a
      · exact Or.inl hva
      by_cases hvb : v = b
      · exact Or.inr (Or.inr hvb)
      exact Or.inr (Or.inl ⟨hvb, hva, hv⟩)
  have hnd : L.Nodup := by
    simp only [L, List.nodup_cons, List.mem_append, Finset.mem_toList,
      List.mem_singleton, T, Finset.mem_erase, List.nodup_append]
    refine ⟨?_, Finset.nodup_toList _, by simp, ?_⟩
    · simp [hab]
    · intro c hc d hd
      have hdb : d = b := by simpa using hd
      subst d
      exact hc.1
  have hchain : L.IsChain G.Adj := by
    apply List.Pairwise.isChain
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hE ((hmem _).mp (List.getElem_mem hi)) ((hmem _).mp (List.getElem_mem hj))
      (fun heq => (Nat.ne_of_lt hij) (hnd.getElem_inj_iff.mp heq))
  let p₀ := SimpleGraph.Walk.ofSupport L (by simp [L]) hchain
  have hfirst : L.head (by simp [L]) = a := rfl
  have hlast : L.getLast (by simp [L]) = b := by
    change ((a :: T.toList) ++ [b]).getLast _ = b
    exact List.getLast_concat
  let p := p₀.copy hfirst hlast
  have hsupport : p.support = L := by simp [p, p₀]
  have hp : p.IsPath := p.isPath_def.mpr (hsupport ▸ hnd)
  refine ⟨p, hp, fun v => by rw [hsupport]; exact hmem v, ?_⟩
  have hset : (p.support.toFinset : Set V) = E := by
    ext v
    simpa [hsupport] using hmem v
  rw [← hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
    SimpleGraph.Walk.length_support]

 
theorem join_disjoint_paths {V : Type*} {G : SimpleGraph V} {a b u v : V}
    (p : G.Walk a b) (q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hbu : G.Adj b u) (hdis : ∀ w ∈ p.support, w ∉ q.support) :
    (p.append (.cons hbu q)).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_cons, List.tail_cons, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro c hc d hd hcd
  subst d
  exact hdis c hc hd

 

theorem attached_clique_long_path {V : Type*} [Fintype V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {s : ℕ} (hs : 4 ≤ s)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H) (hdegree : ∀ a, s ≤ H.degree a)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    {S E : Set V} {u y z w : V} (hu : u ∈ S \ E) (hw : w ∈ E)
    (hy : y ∉ S) (hz : z ∉ S) (hES : E ⊆ S) (hE : H.IsClique E)
    (hconn : ∀ a ∈ S, ∀ b ∈ S, (within H S).Reachable a b)
    (hboundary : ∀ a ∈ S, ∀ b, H.Adj a b → b ∈ S ∨ b = y ∨ b = z)
    (hattach : ∀ a ∈ E, ∀ b, (within H S).Adj a b → b ∈ E ∨ b = u)
    (hentry : ∃ e ∈ E, e ≠ w ∧ (within H S).Adj e u) :
    ∃ v, ∃ p : (within H S).Walk w v, p.IsPath ∧ 2 * s - 2 ≤ p.length + 1 := by
  classical
  let K := within H S
  let D := within H (S \ E)
  have hDK : D ≤ K := fun a b h => ⟨h.1, h.2.1.1, h.2.2.1⟩
  have hScard := deletion_component_card hs hfree hdegree hexpand ⟨u, hu.1⟩ hy hz hboundary
  have hEcard := clique_ncard_lt hfree hE
  have hDcard : 2 ≤ (S \ E).ncard := by
    have := Set.ncard_sdiff_add_ncard_of_subset hES
    omega
  obtain ⟨b, hb, hbu⟩ := exists_mem_ne_of_ncard (w₀ := u) hDcard
  have hreach := reachable_after_removing_attached_set hu hb
    (hconn u hu.1 b hb.1) hattach
  obtain ⟨r₀, hr₀⟩ := hreach.exists_isPath
  obtain ⟨v, r, hr, hmax⟩ := exists_longest_path_from D u
  have hpos : 0 < r.length := by
    have hle := hmax b r₀ hr₀
    have hne : r₀.length ≠ 0 := fun h => hbu (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
    omega
  have hvu : v ≠ u := by
    intro heq
    subst v
    have := (SimpleGraph.Walk.isPath_iff_nil.mp hr).length_eq_zero
    omega
  have hrS := within_support r hu
  have hv : v ∈ S \ E := hrS v r.end_mem_support
  have hnbs : ∀ a, K.Adj v a → a ∈ r.support := by
    intro a ha
    have haE : a ∉ E := by
      intro haE
      rcases hattach a haE v ha.symm with hvE | hvu'
      · exact hv.2 hvE
      · exact hvu hvu'
    exact longest_path_endpoint_neighbors r hr hmax a ⟨ha.1, hv, ha.2.2, haE⟩
  have hvw : v ≠ w := fun heq => hv.2 (heq ▸ hw)
  have hnvw : ¬ H.Adj v w := by
    intro hvw'
    rcases hattach w hw v ⟨hvw'.symm, hES hw, hv.1⟩ with hvE | hvu'
    · exact hv.2 hvE
    · exact hvu hvu'
  let T : Set V := (r.support.toFinset : Set V)
  have hTcard : T.ncard = r.length + 1 := by
    simp only [T, Set.ncard_coe_finset, List.toFinset_card_of_nodup hr.support_nodup,
      SimpleGraph.Walk.length_support]
  have hsub : closedNeighborhood H {v, w} ⊆ insert y (insert z (E ∪ T)) := by
    intro a ha
    rcases ha with ha | ⟨c, hc, hca⟩
    · rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact Or.inr (Or.inr (Or.inr (by simp [T])))
      · have : a = w := Set.mem_singleton_iff.mp ha
        subst a
        exact Or.inr (Or.inr (Or.inl hw))
    · rcases Set.mem_insert_iff.mp hc with hc | hc
      · subst c
        rcases hboundary v hv.1 a hca with haS | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (by simpa [T] using hnbs a ⟨hca, hv.1, haS⟩)))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have : c = w := Set.mem_singleton_iff.mp hc
        subst c
        rcases hboundary w (hES hw) a hca with haS | rfl | rfl
        · rcases hattach w hw a ⟨hca, hES hw, haS⟩ with haE | rfl
          · exact Or.inr (Or.inr (Or.inl haE))
          · exact Or.inr (Or.inr (Or.inr (by simp [T])))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
  have hsum : 2 * s - 2 ≤ E.ncard + (r.length + 1) := by
    have := hexpand v w hvw hnvw
    have := Set.ncard_le_ncard hsub
    have := Set.ncard_insert_le y (insert z (E ∪ T))
    have := Set.ncard_insert_le z (E ∪ T)
    have := Set.ncard_union_le E T
    omega
  obtain ⟨e, he, hew, heu⟩ := hentry
  have hEK : K.IsClique E := fun a ha b hb hab => ⟨hE ha hb hab, hES ha, hES hb⟩
  obtain ⟨q, hq, hqE, hqcard⟩ := clique_path_between hEK hw he hew.symm
  let rK := r.mapLe hDK
  have hrK : rK.IsPath := hr.mapLe hDK
  have hdis : ∀ a ∈ q.support, a ∉ rK.support := by
    intro a ha har
    have har' : a ∈ r.support := by simpa [rK] using har
    exact (hrS a har').2 ((hqE a).mp ha)
  refine ⟨v, q.append (.cons heu rK), join_disjoint_paths q rK hq hrK heu hdis, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
    rK, SimpleGraph.Walk.length_mapLe]
  omega

 
theorem coloured_path {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (s : ℕ) (hs : 4 ≤ s) (hconn : H.Connected)
    (hnb : ¬ H.IsBipartite) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ H)
    (hdegree : ∀ v, s ≤ H.degree v)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).ncard)
    (χ : V → Fin 2) (hnc : ∃ y z, χ y ≠ χ z)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓmax : ℓ ≤ 2 * s - 2) :
    ∃ y z, χ y ≠ χ z ∧ ∃ p : H.Walk y z, p.IsPath ∧ p.length = ℓ := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyzcol⟩ :=
    exists_common_neighbor_different_colours hconn hnb χ hnc
  obtain ⟨S, hxS, hyS, hzS, hSconn, hboundary⟩ := deleted_component hxy.ne hxz.ne
  let K := within H S
  have hKH : K ≤ H := within_le H S
  have hbound : ∀ a ∈ S, ∀ b, H.Adj a b → K.Adj a b ∨ b = y ∨ b = z := by
    intro a ha b hab
    rcases hboundary a ha b hab with hb | hb | hb
    · exact Or.inl ⟨hab, ha, hb⟩
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hb)
  have hKdegree : ∀ a ∈ S, s - 2 ≤ K.degree a := by
    intro a ha
    have := degree_le_add_two_of_boundary (hbound a ha)
    have := hdegree a
    omega
  obtain ⟨v, p, hp, hmax⟩ := exists_longest_path_from K x
  have hpS := within_support p hxS
  have hvS := hpS v p.end_mem_support
  have hprefix : ∀ {a b : V}, H.Adj a y → H.Adj a z →
      (q : K.Walk a b) → q.IsPath → a ∈ S → ℓ ≤ q.length + 1 →
      ∃ y z, χ y ≠ χ z ∧ ∃ r : H.Walk y z, r.IsPath ∧ r.length = ℓ := by
    intro a b hay haz q hq ha hlen
    have hqS := within_support q ha
    apply different_colour_prefix χ hay haz hyzcol (q.mapLe hKH) (hq.mapLe hKH)
    · intro h
      exact hyS (hqS y (by simpa using h))
    · intro h
      exact hzS (hqS z (by simpa using h))
    · exact hℓ
    · simpa using hlen
  by_cases hlen : ℓ ≤ p.length + 1
  · exact hprefix hxy hxz p hp hxS hlen
  have hplen : 0 < p.length := by
    have hpcard : (p.support.toFinset : Set V).ncard = p.length + 1 := by
      simp only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
        SimpleGraph.Walk.length_support]
    have hnbp := longest_path_endpoint_neighbors p hp hmax
    have hc := degree_add_one_le_of_neighbors_subset (G := K) (v := v)
      (S := (p.support.toFinset : Set V)) (by simp)
      (fun w hw => by simpa using hnbp w hw)
    have := hKdegree v hvS
    omega
  let E := pathEnds K x p.support
  have hES : E ⊆ S := fun e he => hpS e (mem_pathEnds_support he)
  have hcl : K.IsClique E := by
    apply pathEnds_isClique p hp hmax
    intro a ha b hb hab hnab
    have haS := hES ha
    have hbS := hES hb
    have hnabH : ¬ H.Adj a b := fun h => hnab ⟨h, haS, hbS⟩
    have hI : ({a, b} : Set V) ⊆ S := by
      intro c hc
      rcases Set.mem_insert_iff.mp hc with hc | hc
      · exact hc ▸ haS
      · exact (Set.mem_singleton_iff.mp hc) ▸ hbS
    have hsub := closedNeighborhood_within_boundary hI hboundary
    have hc := Set.ncard_le_ncard hsub
    have hc₁ := Set.ncard_insert_le y (insert z (closedNeighborhood K {a, b}))
    have hc₂ := Set.ncard_insert_le z (closedNeighborhood K {a, b})
    have he := hexpand a b hab hnabH
    change (closedNeighborhood H {a, b}).ncard ≤
      (insert y (insert z (closedNeighborhood K {a, b}))).ncard at hc
    omega
  have hclH : H.IsClique E := fun a ha b hb hab => hKH (hcl ha hb hab)
  have hEnddeg : ∀ e ∈ E, K.degree e ≤ E.ncard := by
    intro e he
    obtain ⟨q, hq, hperm⟩ := he
    apply degree_le_card_pathEnds q hq hperm
    intro a hea
    exact hperm.mem_iff.mpr (pathEnds_neighbors p hmax ⟨q, hq, hperm⟩ a hea)
  have hvE : v ∈ E := ⟨p, hp, .refl _⟩
  have hEsize : s - 2 ≤ E.ncard := (hKdegree v hvS).trans (hEnddeg v hvE)
  obtain ⟨k, hkpos, hk, hsegment⟩ := pathEnds_final_segment p hp (.refl _) hcl
    (by simp only [SimpleGraph.Walk.length_support]; omega)
  let u := p.getVert (k - 1)
  let w₀ := p.getVert k
  have huS : u ∈ S := hpS u (p.getVert_mem_support _)
  have huE : u ∉ E := by
    intro hu
    have := (hsegment (k - 1) (by omega)).mp hu
    omega
  have hw₀ : w₀ ∈ E := (hsegment k hk).mpr le_rfl
  have huw₀ : K.Adj u w₀ := by
    have := p.adj_getVert_succ (show k - 1 < p.length by omega)
    simpa only [Nat.sub_add_cancel hkpos] using this
  have hyE : y ∉ E := fun h => hyS (hES h)
  have hzE : z ∉ E := fun h => hzS (hES h)
  have huy : u ≠ y := fun heq => hyS (heq ▸ huS)
  have huz : u ≠ z := fun heq => hzS (heq ▸ huS)
  have hEbound : ∀ e ∈ E, ∀ b, H.Adj e b → K.Adj e b ∨ b = y ∨ b = z :=
    fun e he => hbound e (hES he)
  obtain ⟨w₁, hw₁, hw₁ne, huw₁⟩ := endpoint_clique_two_entries hs hfree hdegree
    hclH hEsize hw₀ huE hyE hzE huy huz hEbound
    (fun e he hne => pathEnds_partial_attachment p hp hmax hcl hkpos hk hsegment he hne) hEnddeg
  have hattach := pathEnds_attachment_of_two_entries p hp hmax hcl hkpos hk hsegment
    hw₁ hw₁ne huw₁
  obtain ⟨w, hw, hwy, hwz⟩ := endpoint_clique_common_neighbor hs hfree hdegree
    hclH hEsize huE hyE hzE hEbound hattach hKH
  have hentry : ∃ e ∈ E, e ≠ w ∧ K.Adj e u := by
    by_cases hww₀ : w = w₀
    · exact ⟨w₁, hw₁, fun heq => hw₁ne (heq.trans hww₀), huw₁.symm⟩
    · exact ⟨w₀, hw₀, Ne.symm hww₀, huw₀.symm⟩
  obtain ⟨b, q, hq, hqlen⟩ := attached_clique_long_path hs hfree hdegree hexpand
    ⟨huS, huE⟩ hw hyS hzS hES hclH hSconn hboundary hattach hentry
  exact hprefix hwy hwz q hq (hES hw) (hℓmax.trans hqlen)


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Exceptional
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem neighborhood_compl_clique_of_triangle_free {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G) (v : V) :
    Gᶜ.IsClique (G.neighborSet v) := by
  classical
  intro a ha b hb hab
  refine ⟨hab, fun hadj => ?_⟩
  have hc : G.IsNClique 3 {v, a, b} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hb, hadj⟩
  exact hfree ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp hc.not_cliqueFree)

 
theorem ramsey_three_three_upper : RamseyProperty 3 3 6 := by
  classical
  intro G
  rw [SimpleGraph.cycleGraph_three_eq_top]
  by_contra hn
  obtain ⟨hred, hblue⟩ := not_or.mp hn
  have h₁ := clique_ncard_lt hblue (neighborhood_compl_clique_of_triangle_free hred (0 : Fin 6))
  have hred' : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ Gᶜᶜ := by simpa using hred
  have h₂ := clique_ncard_lt hred' (neighborhood_compl_clique_of_triangle_free hblue (0 : Fin 6))
  rw [ncard_neighborSet] at h₁ h₂
  rw [SimpleGraph.degree_compl] at h₂
  simp only [Fintype.card_fin] at h₂
  omega

 
theorem RamseyProperty.mono {m n N M : ℕ} (h : RamseyProperty m n N) (hNM : N ≤ M) :
    RamseyProperty m n M := by
  intro G
  let f : Fin N → Fin M := Fin.castLE hNM
  let H := G.comap f
  have hc : H ⊑ G := ⟨⟨⟨f, fun {a b} hab => hab⟩, Fin.castLE_injective hNM⟩⟩
  have hcc : Hᶜ ⊑ Gᶜ := by
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, Fin.castLE_injective hNM⟩⟩
    exact ⟨fun heq => hab.1 (Fin.castLE_injective hNM heq), hab.2⟩
  rcases h H with hcycle | hclique
  · exact Or.inl (hcycle.trans hc)
  · exact Or.inr (hclique.trans hcc)

 
theorem ramsey_three_three_lower : ¬ RamseyProperty 3 3 5 := by
  intro h
  have proof5 : ∀ a b c : Fin 5,
      ¬ ((SimpleGraph.cycleGraph 5).Adj a b ∧ (SimpleGraph.cycleGraph 5).Adj a c ∧
        (SimpleGraph.cycleGraph 5).Adj b c) ∧
      ¬ ((SimpleGraph.cycleGraph 5)ᶜ.Adj a b ∧ (SimpleGraph.cycleGraph 5)ᶜ.Adj a c ∧
        (SimpleGraph.cycleGraph 5)ᶜ.Adj b c) := by decide
  have hr : (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact (proof5 a b c).1 ⟨hab, hac, hbc⟩
  have hb : (SimpleGraph.cycleGraph 5)ᶜ.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact (proof5 a b c).2 ⟨hab, hac, hbc⟩
  rcases h (SimpleGraph.cycleGraph 5) with hred | hblue
  · rw [SimpleGraph.cycleGraph_three_eq_top] at hred
    exact hred.not_cliqueFree hr
  · exact hblue.not_cliqueFree hb

 
theorem exceptional : cycleCliqueRamsey 3 3 = 6 := by
  apply le_antisymm
  · exact Nat.sInf_le ramsey_three_three_upper
  · have hmem : RamseyProperty 3 3 (cycleCliqueRamsey 3 3) :=
      Nat.sInf_mem (s := {N | RamseyProperty 3 3 N}) ⟨6, ramsey_three_three_upper⟩
    by_contra hn
    exact ramsey_three_three_lower (hmem.mono (by omega))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Independence
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem indep_ncard_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I : Set V} (hI : G.IsIndepSet I) : I.ncard ≤ G.indepNum := by
  classical
  have hc := (show G.IsIndepSet (I.toFinset : Set V) by simpa using hI).card_le_indepNum
  rwa [← Set.ncard_eq_toFinset_card'] at hc

theorem exists_indep_of_independence {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) : ∃ I ⊆ S, G.IsIndepSet I ∧ I.ncard = independence G S := by
  classical
  obtain ⟨J, hJ⟩ := (G.induce S).exists_isNIndepSet_indepNum
  refine ⟨Subtype.val '' (J : Set S), ?_, ?_, ?_⟩
  · rintro v ⟨w, _, rfl⟩
    exact w.property
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hxy hab
    exact hJ.isIndepSet hx hy (fun heq => hxy (congrArg Subtype.val heq)) hab
  · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    exact hJ.card_eq

theorem indep_ncard_le_independence {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I S : Set V} (hI : G.IsIndepSet I) (hIS : I ⊆ S) : I.ncard ≤ independence G S := by
  classical
  let J : Set S := Subtype.val ⁻¹' I
  have hJ : (G.induce S).IsIndepSet J := by
    intro a ha b hb hab hadj
    exact hI ha hb (fun h => hab (Subtype.ext h)) hadj
  have heq : Subtype.val '' J = I := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hIS hv⟩, hv, rfl⟩
  have hc := indep_ncard_le hJ
  rw [← Set.ncard_image_of_injective J Subtype.val_injective, heq] at hc
  exact hc

theorem independence_mono {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S T : Set V} (hST : S ⊆ T) : independence G S ≤ independence G T := by
  obtain ⟨I, hIS, hI, hcard⟩ := exists_indep_of_independence G S
  rw [← hcard]
  exact indep_ncard_le_independence hI (hIS.trans hST)

theorem independence_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    independence G S ≤ S.ncard := by
  obtain ⟨I, hIS, _, hcard⟩ := exists_indep_of_independence G S
  rw [← hcard]
  exact Set.ncard_le_ncard hIS

theorem independence_pos {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hS : S.Nonempty) : 0 < independence G S := by
  obtain ⟨x, hx⟩ := hS
  have hI : G.IsIndepSet {x} := Set.pairwise_singleton _ _
  have hc := indep_ncard_le_independence hI (Set.singleton_subset_iff.mpr hx)
  simp only [Set.ncard_singleton] at hc
  omega

theorem independence_univ {V : Type*} [Fintype V] (G : SimpleGraph V) :
    independence G Set.univ = G.indepNum := by
  classical
  apply le_antisymm
  · obtain ⟨I, _, hI, hcard⟩ := exists_indep_of_independence G Set.univ
    rw [← hcard]
    exact indep_ncard_le hI
  · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hc := indep_ncard_le_independence hI.isIndepSet (Set.subset_univ _)
    simpa only [Set.ncard_coe_finset, hI.card_eq] using hc

 

theorem independence_outside_closed {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I S : Set V} (hI : G.IsIndepSet I) (hIS : I ⊆ S) :
    independence G (S \ closedNeighborhood G I) + I.ncard ≤ independence G S := by
  classical
  obtain ⟨J, hJsub, hJ, hJcard⟩ := exists_indep_of_independence G
    (S \ closedNeighborhood G I)
  have hdisj : Disjoint J I := Set.disjoint_left.mpr (by
    intro v hv hi
    exact (hJsub hv).2 (Or.inl hi))
  have hJI : G.IsIndepSet (J ∪ I) := by
    intro a ha b hb hab hadj
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hJ ha hb hab hadj
    · exact (hJsub ha).2 (Or.inr ⟨b, hb, hadj.symm⟩)
    · exact (hJsub hb).2 (Or.inr ⟨a, ha, hadj⟩)
    · exact hI ha hb hab hadj
  have hc := indep_ncard_le_independence hJI (Set.union_subset (fun _ h => (hJsub h).1) hIS)
  rwa [Set.ncard_union_eq hdisj, hJcard] at hc

 
theorem no_compl_clique_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) :
    (¬ (⊤ : SimpleGraph (Fin (a + 1))) ⊑ Gᶜ) ↔ G.indepNum ≤ a := by
  classical
  constructor
  · intro h
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hc := clique_ncard_lt h ((SimpleGraph.isClique_compl G).mpr hI.isIndepSet)
    simp only [Set.ncard_coe_finset, hI.card_eq] at hc
    omega
  · intro h hc
    apply hc.not_cliqueFree
    intro I hI
    have hi := (SimpleGraph.isNClique_compl G).mp hI
    have hb := hi.isIndepSet.card_le_indepNum
    rw [hi.card_eq] at hb
    omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_InducedGraphs
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem indep_induce_iff_image {V : Type*} {G : SimpleGraph V} {S : Set V} {I : Set S} :
    (G.induce S).IsIndepSet I ↔ G.IsIndepSet (Subtype.val '' I) := by
  constructor
  · intro h a ha b hb hab hadj
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact h hx hy (fun heq => hab (congrArg Subtype.val heq)) hadj
  · intro h a ha b hb hab hadj
    exact h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (fun heq => hab (Subtype.ext heq)) hadj

theorem independence_induce_image {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) (T : Set S) :
    independence (G.induce S) T = independence G (Subtype.val '' T) := by
  classical
  apply le_antisymm
  · obtain ⟨I, hIT, hI, hc⟩ := exists_indep_of_independence (G.induce S) T
    have hb := indep_ncard_le_independence (indep_induce_iff_image.mp hI) (Set.image_mono hIT)
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective, hc] at hb
  · obtain ⟨I, hIT, hI, hc⟩ := exists_indep_of_independence G (Subtype.val '' T)
    let J : Set S := Subtype.val ⁻¹' I
    have heq : Subtype.val '' J = I := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        obtain ⟨w, _, rfl⟩ := hIT hv
        exact ⟨w, hv, rfl⟩
    have hJ : (G.induce S).IsIndepSet J := indep_induce_iff_image.mpr (heq ▸ hI)
    have hJT : J ⊆ T := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hIT hx
      exact Subtype.val_injective hxy ▸ hy
    have hb := indep_ncard_le_independence hJ hJT
    rw [← Set.ncard_image_of_injective J Subtype.val_injective, heq, hc] at hb
    exact hb

 
theorem independence_add_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A B S : Set V} (hA : A ⊆ S) (hB : B ⊆ S) (hdis : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    independence G A + independence G B ≤ independence G S := by
  classical
  obtain ⟨I, hIA, hI, hcI⟩ := exists_indep_of_independence G A
  obtain ⟨J, hJB, hJ, hcJ⟩ := exists_indep_of_independence G B
  have hdIJ : Disjoint I J := hdis.mono hIA hJB
  have hIJ : G.IsIndepSet (I ∪ J) := by
    intro a ha b hb hab hadj
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hI ha hb hab hadj
    · exact hcross a (hIA ha) b (hJB hb) hadj
    · exact hcross b (hIA hb) a (hJB ha) hadj.symm
    · exact hJ ha hb hab hadj
  have hc := indep_ncard_le_independence hIJ (Set.union_subset (hIA.trans hA) (hJB.trans hB))
  rwa [Set.ncard_union_eq hdIJ, hcI, hcJ] at hc

 
theorem clique_of_independence_le_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hα : independence G S ≤ 1) : G.IsClique S := by
  intro a ha b hb hab
  by_contra hn
  have hI : G.IsIndepSet {a, b} := by
    intro x hx y hy hxy hxyadj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact hn hxyadj
    · exact hn hxyadj.symm
    · exact hxy rfl
  have hc := indep_ncard_le_independence hI (Set.insert_subset ha (Set.singleton_subset_iff.mpr hb))
  rw [Set.ncard_pair hab] at hc
  omega

 
theorem bipartite_card_le_twice_indep {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hbip : G.IsBipartite) : Fintype.card V ≤ 2 * G.indepNum := by
  classical
  obtain ⟨χ⟩ := hbip
  have hzero := indep_ncard_le (χ.isIndepSet_colorClass (0 : Fin 2))
  have hone := indep_ncard_le (χ.isIndepSet_colorClass (1 : Fin 2))
  have hunion : χ.colorClass 0 ∪ χ.colorClass 1 = Set.univ := by
    ext v
    simp only [Set.mem_union, SimpleGraph.Coloring.colorClass, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have := (χ v).isLt
    omega
  have hdis : Disjoint (χ.colorClass 0) (χ.colorClass 1) := by
    apply Set.disjoint_left.mpr
    intro v hv₀ hv₁
    have hzero : χ v = 0 := hv₀
    have hone : χ v = 1 := hv₁
    exact (by decide : (0 : Fin 2) ≠ 1) (hzero.symm.trans hone)
  have hc := Set.ncard_union_eq hdis
  rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card] at hc
  omega

 
theorem closedNeighborhood_singleton_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedNeighborhood G {v}).ncard = G.degree v + 1 := by
  have heq : closedNeighborhood G {v} = insert v (G.neighborSet v) := by
    ext w
    simp [closedNeighborhood, SimpleGraph.mem_neighborSet]
  rw [heq, Set.ncard_insert_of_notMem G.notMem_neighborSet_self, ncard_neighborSet]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Density
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph


theorem minimal_density_connected {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} (hε : ε ≤ 1) (hdense : MinimalDensity G s ε) :
    G.Connected := by
  classical
  simp only [MinimalDensity, Nat.card_eq_fintype_card] at hdense
  obtain ⟨r⟩ := ‹Nonempty V›
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨r, fun w => ?_⟩
  by_contra hw
  let A : Set V := {v | G.Reachable r v}
  have hrA : r ∈ A := SimpleGraph.Reachable.refl r
  have hwA : w ∈ Aᶜ := hw
  have hsum := Set.ncard_add_ncard_compl A
  rw [Nat.card_eq_fintype_card] at hsum
  have hApos : 0 < A.ncard := (Set.ncard_pos).mpr ⟨r, hrA⟩
  have hBpos : 0 < Aᶜ.ncard := (Set.ncard_pos).mpr ⟨w, hwA⟩
  have hA := hdense.2 A ⟨r, hrA⟩ (by omega)
  have hB := hdense.2 Aᶜ ⟨w, hwA⟩ (by omega)
  have hα := independence_add_le (G := G) (Set.subset_univ A) (Set.subset_univ Aᶜ)
    disjoint_compl_right (by
      intro a ha b hb hab
      exact hb (ha.trans hab.reachable))
  rw [independence_univ] at hα
  have hmul := Nat.mul_le_mul_left s hα
  have hd := hdense.1
  nlinarith

 

theorem minimal_density_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s ε : ℕ} (hdense : MinimalDensity G s ε)
    {I : Set V} (hI : G.IsIndepSet I) (hne : I.Nonempty) :
    s * I.ncard ≤ (closedNeighborhood G I).ncard ∧
    ((0 < ε ∨ (closedNeighborhood G I)ᶜ.Nonempty) →
      s * I.ncard < (closedNeighborhood G I).ncard) := by
  classical
  simp only [MinimalDensity, Nat.card_eq_fintype_card] at hdense
  let N := closedNeighborhood G I
  have hNpos : 0 < N.ncard := (Set.ncard_pos).mpr (hne.mono (fun _ h => Or.inl h))
  have hsum := Set.ncard_add_ncard_compl N
  rw [Nat.card_eq_fintype_card] at hsum
  have hα := independence_outside_closed hI (Set.subset_univ I)
  rw [independence_univ, ← Set.compl_eq_univ_sdiff] at hα
  have hm := Nat.mul_le_mul_left s hα
  have hd := hdense.1
  by_cases hR : Nᶜ.Nonempty
  · have hr := hdense.2 Nᶜ hR (by omega)
    have hstrict : s * I.ncard < N.ncard := by nlinarith
    exact ⟨hstrict.le, fun _ => hstrict⟩
  · have hRcard : Nᶜ.ncard = 0 := (Set.ncard_eq_zero).mpr (Set.not_nonempty_iff_eq_empty.mp hR)
    refine ⟨?_, ?_⟩
    · nlinarith
    · rintro (he | hn)
      · nlinarith
      · exact False.elim (hR hn)

 
theorem exists_minimal_density {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s ε : ℕ) {D : Set V} (hne : D.Nonempty)
    (hd : s * independence G D + ε ≤ D.ncard) :
    ∃ S ⊆ D, S.Nonempty ∧ MinimalDensity (G.induce S) s ε := by
  classical
  let A : Set ℕ := {n | ∃ S ⊆ D, S.Nonempty ∧
    s * independence G S + ε ≤ S.ncard ∧ S.ncard = n}
  have hA : A.Nonempty := ⟨D.ncard, D, Set.Subset.rfl, hne, hd, rfl⟩
  obtain ⟨S, hSD, hS, hdS, hcS⟩ := Nat.sInf_mem hA
  refine ⟨S, hSD, hS, ?_, ?_⟩
  · simpa [independence, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hdS
  · intro T hT hlt
    by_contra hn
    have him : Subtype.val '' T ⊆ D := by
      rintro x ⟨y, hy, rfl⟩
      exact hSD y.property
    have hcard : (Subtype.val '' T).ncard = T.ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    have hm : (Subtype.val '' T).ncard ∈ A := by
      refine ⟨Subtype.val '' T, him, hT.image _, ?_, rfl⟩
      rw [← independence_induce_image, hcard]
      omega
    have hmin := Nat.sInf_le hm
    rw [hcard, ← hcS] at hmin
    have hSc : S.ncard = Nat.card S := (Nat.card_coe_set_eq S).symm
    omega

 
theorem minimal_density_indep_ge_two {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} (hd : MinimalDensity G s ε)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ G) : 2 ≤ G.indepNum := by
  classical
  have hpos : 0 < G.indepNum := by
    simpa [independence_univ] using
      (independence_pos (G := G) (S := Set.univ) Set.univ_nonempty)
  by_contra hn
  have ha : G.indepNum = 1 := by omega
  have hcl : G.IsClique Set.univ := clique_of_independence_le_one (by
    rw [independence_univ, ha])
  have hlt := clique_ncard_lt hfree hcl
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hlt
  have hc := hd.1
  rw [ha, Nat.mul_one, Nat.card_eq_fintype_card] at hc
  omega

 

theorem minimal_density_properties {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} [DecidableRel G.Adj] (hs : 4 ≤ s) (hε : ε ≤ 1)
    (hd : MinimalDensity G s ε) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ G) :
    G.Connected ∧ ¬ G.IsBipartite ∧ 2 * s + ε ≤ Fintype.card V ∧
    (∀ v, s ≤ G.degree v) ∧
    (∀ I, G.IsIndepSet I → I.Nonempty →
      s * I.ncard ≤ (closedNeighborhood G I).ncard ∧
      ((0 < ε ∨ (closedNeighborhood G I)ᶜ.Nonempty) →
        s * I.ncard < (closedNeighborhood G I).ncard)) := by
  classical
  have hcV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hα := minimal_density_indep_ge_two hd hfree
  have horder : 2 * s + ε ≤ Fintype.card V := by
    have := hd.1
    nlinarith
  refine ⟨minimal_density_connected hε hd, ?_, horder, ?_,
    fun I hI hne => minimal_density_expansion hd hI hne⟩
  · intro hbip
    have hupper := bipartite_card_le_twice_indep hbip
    have hlower := hd.1
    nlinarith
  · intro v
    have hexp := minimal_density_expansion hd
      (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.singleton_nonempty v)
    simp only [Set.ncard_singleton, Nat.mul_one, closedNeighborhood_singleton_card] at hexp
    by_cases hR : (closedNeighborhood G {v})ᶜ.Nonempty
    · have := hexp.2 (Or.inr hR)
      omega
    · have hN : closedNeighborhood G {v} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro w
        by_contra hw
        exact hR ⟨w, hw⟩
      have hc := closedNeighborhood_singleton_card G v
      rw [hN, Set.ncard_univ, Nat.card_eq_fintype_card] at hc
      omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_DistanceLayers
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem ncard_union_layers {V : Type*} [Fintype V] {ι : Type*}
    (D : ι → Set V) (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (F : Finset ι) : (⋃ i ∈ F, D i).ncard = ∑ i ∈ F, (D i).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    rw [hu, Set.ncard_union_eq, Finset.sum_insert hi, ih]
    apply Set.disjoint_left.mpr
    intro v hvi hvF
    obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
    exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj

 
theorem sum_independence_layers {V : Type*} [Fintype V] {ι : Type*}
    (G : SimpleGraph V) (D : ι → Set V)
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (F : Finset ι)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      ∀ x ∈ D i, ∀ y ∈ D j, ¬ G.Adj x y) :
    ∑ i ∈ F, independence G (D i) ≤ independence G (⋃ i ∈ F, D i) := by
  classical
  revert hsep
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    intro hsep
    have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
    rw [hu, Finset.sum_insert hi]
    have hD : Disjoint (D i) (⋃ j ∈ F, D j) := by
      apply Set.disjoint_left.mpr
      intro v hvi hvF
      obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
      exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj
    calc
      _ ≤ independence G (D i) + independence G (⋃ j ∈ F, D j) := by
        exact Nat.add_le_add_left (ih (fun j hj l hl hne =>
          hsep j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) hne)) _
      _ ≤ _ := independence_add_le Set.subset_union_left Set.subset_union_right hD (by
        intro x hx y hy
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
        exact hsep i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj) x hx y hyj)


theorem distanceLayer_disjoint {V : Type*} (G : SimpleGraph V) (r : V) :
    Pairwise (fun i j => Disjoint (distanceLayer G r i) (distanceLayer G r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hv₁ hv₂
  exact hij (hv₁.2.symm.trans hv₂.2)

theorem distanceLayer_no_edge {V : Type*} {G : SimpleGraph V} {r : V}
    {i j : ℕ} (hne : i ≠ j) (hpar : i % 2 = j % 2)
    {x y : V} (hx : x ∈ distanceLayer G r i) (hy : y ∈ distanceLayer G r j) :
    ¬ G.Adj x y := by
  intro hxy
  have hd := hxy.diff_dist_adj (u := r)
  rw [hx.2, hy.2] at hd
  omega


theorem paritySum_add_prev (α : ℕ → ℕ) {i : ℕ} (hi : 1 ≤ i) :
    paritySum α i + paritySum α (i - 1) = ∑ j ∈ Finset.range (i + 1), α j := by
  unfold paritySum parityIndices
  rw [Finset.sum_filter, Finset.sum_filter]
  have hip : i - 1 + 1 = i := by omega
  rw [hip]
  have hpar : i % 2 ≠ (i - 1) % 2 := by omega
  have hex : (∑ j ∈ Finset.range i, if j % 2 = (i - 1) % 2 then α j else 0) =
      ∑ j ∈ Finset.range (i + 1), if j % 2 = (i - 1) % 2 then α j else 0 := by
    rw [Finset.sum_range_succ, ite_eq_right hpar, Nat.add_zero]
  rw [hex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : j % 2 = i % 2
  · have hne : j % 2 ≠ (i - 1) % 2 := by omega
    simp only [ite_eq_left he, ite_eq_right hne, Nat.add_zero]
  · have he' : j % 2 = (i - 1) % 2 := by omega
    simp only [ite_eq_right he, ite_eq_left he', Nat.zero_add]

 
theorem parity_independence_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : V) (i : ℕ) :
    paritySum (fun j => independence G (distanceLayer G r j)) i ≤ G.indepNum := by
  apply le_trans (sum_independence_layers G (distanceLayer G r)
    (distanceLayer_disjoint G r) (parityIndices i) ?_)
  · simpa [independence_univ] using
      (independence_mono (G := G) (Set.subset_univ (⋃ j ∈ parityIndices i, distanceLayer G r j)))
  · intro j hj l hl hne x hx y hy
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range] at hj hl
    exact distanceLayer_no_edge hne (hj.2.trans hl.2.symm) hx hy

@[simp] theorem independence_singleton {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) : independence G {v} = 1 := by
  have hp := independence_pos (G := G) (Set.singleton_nonempty v)
  have hc := independence_le_card G {v}
  simp only [Set.ncard_singleton] at hc
  omega

 
theorem distanceLayer_one_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 1 ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    (distanceLayer G r 1).Nonempty := by
  classical
  have h := hexp {r} (Set.pairwise_singleton _ _) (Set.singleton_nonempty r)
  simp only [Set.ncard_singleton, Nat.mul_one, closedNeighborhood_singleton_card] at h
  have hpos : 0 < (G.neighborSet r).ncard := by
    rw [ncard_neighborSet]
    omega
  obtain ⟨v, hv⟩ := (Set.ncard_pos).mp hpos
  have hr : G.Adj r v := hv
  exact ⟨v, hr.reachable, G.dist_eq_one_iff_adj.mpr hr⟩

 
theorem parity_layer_union_nonempty {V : Type*} {G : SimpleGraph V} {r : V}
    (hD : (distanceLayer G r 1).Nonempty) (i : ℕ) :
    (⋃ j ∈ parityIndices i, distanceLayer G r j).Nonempty := by
  by_cases hi : i % 2 = 0
  · refine ⟨r, Set.mem_iUnion₂.mpr ⟨0, ?_, ?_⟩⟩
    · simp [parityIndices, hi]
    · simp
  · obtain ⟨v, hv⟩ := hD
    refine ⟨v, Set.mem_iUnion₂.mpr ⟨1, ?_, hv⟩⟩
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range]
    omega

 
theorem closedNeighborhood_parity_layers {V : Type*} {G : SimpleGraph V}
    {r : V} {i : ℕ} {I : Set V}
    (hI : I ⊆ ⋃ j ∈ parityIndices i, distanceLayer G r j) :
    closedNeighborhood G I ⊆ ⋃ j ∈ Finset.range (i + 2), distanceLayer G r j := by
  intro v hv
  rcases hv with hv | ⟨w, hw, hwv⟩
  · obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp (hI hv)
    have hji : j < i + 1 := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    exact Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), hvj⟩
  · obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp (hI hw)
    have hji : j < i + 1 := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    have hd := hwv.diff_dist_adj (u := r)
    rw [hwj.2] at hd
    exact Set.mem_iUnion₂.mpr ⟨G.dist r v, Finset.mem_range.mpr (by omega),
      hwj.1.trans hwv.reachable, rfl⟩

 
theorem distance_layer_sum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 1 ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (r : V) {i : ℕ} (hi : 1 ≤ i) :
    k * paritySum (fun j => independence G (distanceLayer G r j)) (i - 1) ≤
      ∑ j ∈ Finset.range i, (distanceLayer G r (j + 1)).ncard := by
  classical
  let U := ⋃ j ∈ parityIndices (i - 1), distanceLayer G r j
  have hUne := parity_layer_union_nonempty (distanceLayer_one_nonempty hk hexp r) (i - 1)
  obtain ⟨I, hIU, hI, hcI⟩ := exists_indep_of_independence G U
  have hneI : I.Nonempty := (Set.ncard_pos).mp (by
    rw [hcI]
    exact independence_pos hUne)
  have hp : paritySum (fun j => independence G (distanceLayer G r j)) (i - 1) ≤
      independence G U := by
    apply sum_independence_layers G (distanceLayer G r) (distanceLayer_disjoint G r)
    intro j hj l hl hne x hx y hy
    simp only [parityIndices, Finset.mem_filter, Finset.mem_range] at hj hl
    exact distanceLayer_no_edge hne (hj.2.trans hl.2.symm) hx hy
  have hN := closedNeighborhood_parity_layers hIU
  have hcard := Set.ncard_le_ncard hN
  rw [ncard_union_layers _ (distanceLayer_disjoint G r)] at hcard
  have hii : i - 1 + 2 = i + 1 := by omega
  rw [hii, Finset.sum_range_succ', distanceLayer_zero, Set.ncard_singleton] at hcard
  have he := hexp I hI hneI
  have hm := Nat.mul_le_mul_left k hp
  rw [← hcI] at hm
  omega

 

theorem exists_dense_layer_numeric (α n : ℕ → ℕ) {s ε : ℕ}
    (hs : 4 ≤ s) (hε : ε ≤ 1) (hα₀ : α 0 = 1) (hn₁ : 0 < n 1)
    (hpbound : ∀ i, paritySum α i ≤ 2 * s + ε)
    (hlayer : ∀ i, 1 ≤ i → i ≤ s →
      (2 * s + ε) * paritySum α (i - 1) ≤ ∑ j ∈ Finset.range i, n (j + 1)) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ 0 < n i ∧ s * α i + ε ≤ n i := by
  classical
  by_contra hn
  push Not at hn
  have hweak : ∀ i, 1 ≤ i → i ≤ s → n i ≤ s * α i := by
    intro i hi his
    by_cases hni : 0 < n i
    · have := hn i hi his hni
      omega
    · omega
  have hsum : ∀ i, 1 ≤ i → i ≤ s →
      (∑ j ∈ Finset.range i, n (j + 1)) ≤ s * ∑ j ∈ Finset.range i, α (j + 1) := by
    intro i hi his
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact hweak (j + 1) (by omega) (by omega)
  have hstrict : ε = 0 → ∀ i, 1 ≤ i → i ≤ s →
      (∑ j ∈ Finset.range i, n (j + 1)) < s * ∑ j ∈ Finset.range i, α (j + 1) := by
    intro he i hi his
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro j hj
      have hj' := Finset.mem_range.mp hj
      exact hweak (j + 1) (by omega) (by omega)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have := hn 1 (by omega) (by omega) hn₁
      simpa [he] using this
  have hid : ∀ i, 1 ≤ i →
      (∑ j ∈ Finset.range i, α (j + 1)) + 1 = paritySum α i + paritySum α (i - 1) := by
    intro i hi
    have h := paritySum_add_prev α hi
    rw [Finset.sum_range_succ', hα₀] at h
    exact h.symm
  have hstep : ∀ i, 1 ≤ i → i ≤ s → 0 < paritySum α (i - 1) →
      paritySum α (i - 1) + 2 ≤ paritySum α i := by
    intro i hi his hp
    have hl := hlayer i hi his
    have hw := hsum i hi his
    have heq := hid i hi
    by_contra hbad
    have hcomp := Nat.mul_le_mul_left s
      (show paritySum α i ≤ paritySum α (i - 1) + 1 by omega)
    by_cases he : ε = 0
    · have hst := hstrict he i hi his
      rw [he, Nat.add_zero] at hl
      nlinarith
    · have he₁ : ε = 1 := by omega
      rw [he₁] at hl
      nlinarith
  have hgrowth : ∀ i, i ≤ s → 2 * i + 1 ≤ paritySum α i := by
    intro i
    induction i with
    | zero => simp [hα₀]
    | succ i ih =>
      intro his
      have hi := ih (by omega)
      have hst := hstep (i + 1) (by omega) his (by simpa using (show 0 < paritySum α i by omega))
      simp only [Nat.add_sub_cancel] at hst
      omega
  have hupper := hpbound s
  by_cases he : ε = 0
  · have := hgrowth s (by omega)
    omega
  · have he₁ : ε = 1 := by omega
    have hprev := hgrowth (s - 1) (by omega)
    have hppos : s < paritySum α (s - 1) := by omega
    have hlast : paritySum α (s - 1) + 3 ≤ paritySum α s := by
      have hl := hlayer s (by omega) (by omega)
      rw [he₁] at hl
      have hw := hsum s (by omega) (by omega)
      have heq := hid s (by omega)
      by_contra hbad
      have hcomp := Nat.mul_le_mul_left s
        (show paritySum α s ≤ paritySum α (s - 1) + 2 by omega)
      nlinarith
    omega

 
theorem exists_dense_distance_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    ∃ i, 1 ≤ i ∧ i ≤ k / 2 ∧ (distanceLayer G r i).Nonempty ∧
      (k / 2) * independence G (distanceLayer G r i) + k % 2 ≤
        (distanceLayer G r i).ncard := by
  classical
  have hmod : 2 * (k / 2) + k % 2 = k := by omega
  obtain ⟨i, hi, his, hpos, hd⟩ := exists_dense_layer_numeric
    (fun j => independence G (distanceLayer G r j))
    (fun j => (distanceLayer G r j).ncard)
    (s := k / 2) (ε := k % 2) (by omega) (by omega) (by simp)
    ((Set.ncard_pos).mpr (distanceLayer_one_nonempty (by omega) hexp r))
    (by intro i; rw [hmod]; exact (parity_independence_bound G r i).trans hα)
    (by intro i hi his; rw [hmod]; exact distance_layer_sum (by omega) hexp r hi)
  exact ⟨i, hi, his, (Set.ncard_pos).mp hpos, hd⟩

 
theorem exists_minimal_dense_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) (r : V) :
    ∃ i, 1 ≤ i ∧ i ≤ k / 2 ∧ ∃ S ⊆ distanceLayer G r i,
      S.Nonempty ∧ MinimalDensity (G.induce S) (k / 2) (k % 2) := by
  obtain ⟨i, hi, his, hD, hd⟩ := exists_dense_distance_layer hk hα hexp r
  obtain ⟨S, hSD, hS, hmin⟩ := exists_minimal_density G (k / 2) (k % 2) hD hd
  exact ⟨i, hi, his, S, hSD, hS, hmin⟩

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_BreadthFirst
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exists_distance_predecessor {V : Type*} {G : SimpleGraph V} {r v : V}
    (hv : G.Reachable r v) (hne : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.Reachable r w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hv.symm.exists_walk_length_eq_dist
  rw [G.dist_comm] at hp
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons v w r hvw p =>
    refine ⟨w, hvw, p.reachable.symm, ?_⟩
    have hle : G.dist r w ≤ p.length := by
      simpa only [G.dist_comm] using G.dist_le p
    have htri := hvw.reachable.dist_triangle_right r
    have htri' := hvw.symm.reachable.dist_triangle_right r
    rw [G.dist_eq_one_iff_adj.mpr hvw] at htri
    rw [G.dist_eq_one_iff_adj.mpr hvw.symm] at htri'
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega



theorem exists_breadthFirstParent {V : Type*} (G : SimpleGraph V) (r : V) :
    Nonempty (BreadthFirstParent G r) := by
  classical
  let f : V → V := fun v => if h : G.Reachable r v ∧ v ≠ r then
    (exists_distance_predecessor h.1 h.2).choose else v
  refine ⟨⟨f, ?_⟩⟩
  intro v hv hne
  dsimp [f]
  rw [dite_eq_left ⟨hv, hne⟩]
  exact (exists_distance_predecessor hv hne).choose_spec

 
theorem BreadthFirstParent.iterate_depth {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {v : V} (hv : G.Reachable r v)
    (n : ℕ) (hn : n ≤ G.dist r v) :
    G.Reachable r (B.parent^[n] v) ∧ G.dist r (B.parent^[n] v) + n = G.dist r v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have hn' : n ≤ G.dist r v := by omega
    obtain ⟨hr, hd⟩ := ih hn'
    have hne : B.parent^[n] v ≠ r := by
      intro heq
      rw [heq, G.dist_self] at hd
      omega
    obtain ⟨ha, hr', hd'⟩ := B.step _ hr hne
    rw [Function.iterate_succ_apply']
    exact ⟨hr', by omega⟩

 
theorem BreadthFirstParent.exists_upward_walk {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {v : V} (hv : G.Reachable r v)
    (n : ℕ) (hn : n ≤ G.dist r v) :
    ∃ p : G.Walk v (B.parent^[n] v), p.IsPath ∧ p.length = n ∧
      ∀ w ∈ p.support, ∃ j, j ≤ n ∧ w = B.parent^[j] v := by
  induction n with
  | zero =>
    refine ⟨.nil, by simp, rfl, ?_⟩
    intro w hw
    refine ⟨0, by omega, ?_⟩
    simpa using hw
  | succ n ih =>
    obtain ⟨p, hp, hlen, hsupp⟩ := ih (by omega)
    obtain ⟨hr, hd⟩ := B.iterate_depth hv n (by omega)
    obtain ⟨ha, _, _⟩ := B.step _ hr (by
      intro heq
      rw [heq, G.dist_self] at hd
      omega)
    have hadj : G.Adj (B.parent^[n] v) (B.parent^[n + 1] v) := by
      simpa only [Function.iterate_succ_apply'] using ha
    have hnot : B.parent^[n + 1] v ∉ p.support := by
      intro hw
      obtain ⟨j, hj, heq⟩ := hsupp _ hw
      have h₁ := (B.iterate_depth hv (n + 1) hn).2
      have h₂ := (B.iterate_depth hv j (by omega)).2
      rw [heq] at h₁
      omega
    refine ⟨p.concat hadj, hp.concat hnot hadj, by rw [SimpleGraph.Walk.length_concat, hlen], ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · obtain ⟨j, hj, heq⟩ := hsupp w hw
      exact ⟨j, by omega, heq⟩
    · exact ⟨n + 1, by omega, rfl⟩


theorem layerAncestor_depth {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i j : ℕ}
    (hv : v ∈ distanceLayer G r i) (hj : j ≤ i) :
    G.Reachable r (layerAncestor B i v j) ∧ G.dist r (layerAncestor B i v j) = j := by
  have h := B.iterate_depth hv.1 (i - j) (by rw [hv.2]; omega)
  rw [hv.2] at h
  exact ⟨h.1, by dsimp [layerAncestor]; omega⟩

theorem layerAncestor_root {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i : ℕ} (hv : v ∈ distanceLayer G r i) :
    layerAncestor B i v 0 = r := by
  obtain ⟨hr, hd⟩ := layerAncestor_depth B hv (Nat.zero_le i)
  exact (hr.dist_eq_zero_iff.mp hd).symm

 
theorem layerAncestor_coherent {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {i j l : ℕ} (hjl : j ≤ l) (hli : l ≤ i) (v : V) :
    B.parent^[l - j] (layerAncestor B i v l) = layerAncestor B i v j := by
  unfold layerAncestor
  rw [← Function.iterate_add_apply]
  congr 1
  omega

 

theorem exists_ancestor_path {V : Type*} {G : SimpleGraph V} {r v : V}
    (B : BreadthFirstParent G r) {i j : ℕ}
    (hv : v ∈ distanceLayer G r i) (hj : j ≤ i) :
    ∃ p : G.Walk v (layerAncestor B i v j), p.IsPath ∧ p.length = i - j ∧
      ∀ w ∈ p.support, j ≤ G.dist r w ∧ G.dist r w ≤ i ∧
        layerAncestor B i v (G.dist r w) = w := by
  obtain ⟨p, hp, hlen, hs⟩ := B.exists_upward_walk hv.1 (i - j) (by rw [hv.2]; omega)
  refine ⟨p, hp, hlen, ?_⟩
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hs w hw
  have hd := (B.iterate_depth hv.1 t (by rw [hv.2]; omega)).2
  rw [hv.2] at hd
  refine ⟨by omega, by omega, ?_⟩
  unfold layerAncestor
  rw [show i - G.dist r (B.parent^[t] v) = t by omega]

 

theorem exists_layer_split {V : Type*} {G : SimpleGraph V} {r : V}
    (B : BreadthFirstParent G r) {i : ℕ} {S : Set V}
    (hS : S ⊆ distanceLayer G r i) (hne : ∃ x ∈ S, ∃ y ∈ S, x ≠ y) :
    ∃ d, d < i ∧ ∃ c, (∀ v ∈ S, layerAncestor B i v d = c) ∧
      ∃ x ∈ S, ∃ y ∈ S, layerAncestor B i x (d + 1) ≠ layerAncestor B i y (d + 1) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  let P : ℕ → Prop := fun d => ∀ v ∈ S, layerAncestor B i v d = layerAncestor B i x d
  have h₀ : P 0 := by
    intro v hv
    rw [layerAncestor_root B (hS hv), layerAncestor_root B (hS hx)]
  let d := Nat.findGreatest P i
  have hd : d ≤ i := Nat.findGreatest_le i
  have hPd : P d := Nat.findGreatest_spec (Nat.zero_le i) h₀
  have hdlt : d < i := by
    by_contra hn
    have he : d = i := by omega
    have hh := hPd y hy
    simp only [he, layerAncestor_self] at hh
    exact hxy hh.symm
  refine ⟨d, hdlt, layerAncestor B i x d, hPd, ?_⟩
  by_contra hn
  push Not at hn
  have hPnext : P (d + 1) := by
    intro v hv
    exact hn v hv x hx
  have hh := Nat.le_findGreatest (by omega : d + 1 ≤ i) hPnext
  change d + 1 ≤ d at hh
  omega

theorem path_start_not_mem_tail {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : x ∉ p.support.tail := by
  have hn := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hn
  exact hn.1

 

theorem exists_branch_path {V : Type*} {G : SimpleGraph V} {r y z : V}
    (B : BreadthFirstParent G r) {i d : ℕ}
    (hy : y ∈ distanceLayer G r i) (hz : z ∈ distanceLayer G r i) (hd : d < i)
    (hcommon : layerAncestor B i y d = layerAncestor B i z d)
    (hbranch : layerAncestor B i y (d + 1) ≠ layerAncestor B i z (d + 1)) :
    ∃ p : G.Walk y z, p.IsPath ∧ p.length = 2 * (i - d) ∧
      ∀ w ∈ p.support, G.dist r w = i → w = y ∨ w = z := by
  obtain ⟨p, hp, hplen, hps⟩ := exists_ancestor_path B hy hd.le
  obtain ⟨q, hq, hqlen, hqs⟩ : ∃ q : G.Walk z (layerAncestor B i y d),
      q.IsPath ∧ q.length = i - d ∧ ∀ w ∈ q.support,
        d ≤ G.dist r w ∧ G.dist r w ≤ i ∧ layerAncestor B i z (G.dist r w) = w := by
    obtain ⟨q, hq, hl, hs⟩ := exists_ancestor_path B hz hd.le
    refine ⟨q.copy rfl hcommon.symm, by simpa using hq, by simpa using hl, ?_⟩
    simpa only [SimpleGraph.Walk.support_copy] using hs
  have hinter : ∀ w ∈ p.support, w ∈ q.support → w = layerAncestor B i y d := by
    intro w hw hwq
    obtain ⟨hwd, hwi, hye⟩ := hps w hw
    obtain ⟨_, _, hze⟩ := hqs w hwq
    by_cases he : G.dist r w = d
    · simpa only [he] using hye.symm
    · have hdl : d + 1 ≤ G.dist r w := by omega
      have h₁ := layerAncestor_coherent B hdl hwi y
      have h₂ := layerAncestor_coherent B hdl hwi z
      rw [hye] at h₁
      rw [hze] at h₂
      exact False.elim (hbranch (h₁.symm.trans h₂))
  refine ⟨p.append q.reverse, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append']
    refine ⟨hp.support_nodup, hq.reverse.support_nodup.tail, ?_⟩
    apply List.disjoint_left.mpr
    intro w hw hwq
    have hwq' : w ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hwq
    have he := hinter w hw hwq'
    subst w
    exact path_start_not_mem_tail q.reverse hq.reverse hwq
  · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hplen, hqlen]
    omega
  · intro w hw hwi
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · have hh := (hps w hw).2.2
      simpa only [hwi, layerAncestor_self] using Or.inl hh.symm
    · have hwq : w ∈ q.support := by
        simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hw
      have hh := (hqs w hwq).2.2
      simpa only [hwi, layerAncestor_self] using Or.inr hh.symm

 

theorem cycle_of_layer_path {V : Type*} {G : SimpleGraph V} {r y z : V} {i : ℕ}
    (p : G.Walk y z) (hp : p.IsPath)
    (hplay : ∀ w ∈ p.support, G.dist r w = i)
    (q : G.Walk y z) (hq : q.IsPath) (hqlen : 1 < q.length)
    (hqint : ∀ w ∈ q.support, G.dist r w = i → w = y ∨ w = z) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · apply List.disjoint_left.mpr
    intro w hwp hwq
    have hwp' := List.mem_of_mem_tail hwp
    have hwq' : w ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using List.mem_of_mem_tail hwq
    rcases hqint w hwq' (hplay w hwp') with rfl | rfl
    · exact path_start_not_mem_tail p hp hwp
    · exact path_start_not_mem_tail q.reverse hq.reverse hwq
  · exact Or.inr (by simpa only [SimpleGraph.Walk.length_reverse] using hqlen)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LongPaths
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem path_close_cycle {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) (hlen : 2 ≤ p.length) (hyx : G.Adj y x) :
    (SimpleGraph.Walk.cons hyx p).IsCycle := by
  apply (p.cons_isCycle_iff hyx).mpr
  refine ⟨hp, ?_⟩
  intro he
  have hn := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
  omega

 

theorem extend_nonspanning_cycle {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {x : V} (c : G.Walk x x) (hc : c.IsCycle)
    (hout : ∃ z, z ∉ c.support) :
    ∃ u v, ∃ p : G.Walk u v, p.IsPath ∧ p.length = c.length := by
  classical
  obtain ⟨z, hz⟩ := hout
  obtain ⟨w⟩ := hconn.preconnected x z
  obtain ⟨d, _, hd, hdz⟩ := w.exists_boundary_dart {v | v ∈ c.support} c.start_mem_support hz
  let q := c.rotate d.fst hd
  have hq : q.IsCycle := hc.rotate hd
  have hlen : q.length = c.length := c.length_rotate _ _
  have hnot : d.snd ∉ q.tail.reverse.support := by
    intro hm
    have hm₁ : d.snd ∈ q.tail.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hm
    have hm₂ : d.snd ∈ q.support := q.isSubwalk_rfl.tail.support_subset hm₁
    exact hdz ((c.mem_support_rotate_iff _ _).mp hm₂)
  let p := SimpleGraph.Walk.cons d.adj.symm q.tail.reverse
  refine ⟨d.snd, _, p, ?_, ?_⟩
  · exact hq.isPath_tail.reverse.cons hnot
  · have hl := hc.three_le_length
    simp only [p, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.length_tail, hlen]
    omega

 

theorem long_path_min_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d) (hconn : G.Connected)
    (hdegree : ∀ v, d ≤ G.degree v) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧ min (Fintype.card V) (2 * d + 1) ≤ p.length + 1 := by
  classical
  let : Nonempty V := hconn.nonempty
  obtain ⟨x, y, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨x, y, p, hp, ?_⟩
  by_contra hn
  have hlen : p.length < 2 * d := by omega
  have horder : p.length + 1 < Fintype.card V := by omega
  let W : Set V := {v | v ∈ p.support}
  have hWcard : W.ncard = p.length + 1 := by
    have heq : W = (p.support.toFinset : Set V) := by ext v; simp [W]
    rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support]
  have hnb : ∀ v, G.Adj y v → v ∈ p.support :=
    longest_path_endpoint_neighbors p hp (fun v q hq => hmax x v q hq)
  have hxnb : ∀ v, G.Adj x v → v ∈ p.support := by
    intro v hv
    have := longest_path_endpoint_neighbors p.reverse hp.reverse
      (fun v q hq => by simpa using hmax y v q hq) v hv
    simpa using this
  have hlower : d ≤ p.length := by
    have hc := degree_add_one_le_of_neighbors_subset (G := G) (v := y)
      (show y ∈ W from p.end_mem_support) (fun v hv => hnb v hv)
    rw [hWcard] at hc
    have := hdegree y
    omega
  let E := pathEnds G x p.support
  have hE : d ≤ E.ncard :=
    (hdegree y).trans (degree_le_card_pathEnds p hp (List.Perm.refl _) hnb)
  have hxE : x ∉ E := pathEnds_no_start (by rw [SimpleGraph.Walk.length_support]; omega)
  have hex : ∃ e, e ∈ E ∧ G.Adj x e := by
    by_contra hne
    push Not at hne
    have hdis : Disjoint E (G.neighborSet x) := by
      exact Set.disjoint_left.mpr (fun e he hn => hne e he hn)
    have hins : insert x (E ∪ G.neighborSet x) ⊆ W := by
      intro v hv
      rcases hv with rfl | hv
      · exact p.start_mem_support
      · rcases hv with hv | hv
        · exact mem_pathEnds_support hv
        · exact hxnb v hv
    have hnot : x ∉ E ∪ G.neighborSet x := by simp [hxE]
    have hc := Set.ncard_le_ncard hins
    rw [Set.ncard_insert_of_notMem hnot, Set.ncard_union_eq hdis,
      ncard_neighborSet, hWcard] at hc
    have hxdeg := hdegree x
    omega
  obtain ⟨e, he, hxe⟩ := hex
  obtain ⟨q, hq, hperm⟩ := he
  have hqlen : q.length = p.length := by
    have := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  let c := SimpleGraph.Walk.cons hxe.symm q
  have hc : c.IsCycle := path_close_cycle q hq (by omega) hxe.symm
  have hout : ∃ z, z ∉ c.support := by
    have hnW : W ≠ Set.univ := by
      intro heq
      rw [heq, Set.ncard_univ, Nat.card_eq_fintype_card] at hWcard
      omega
    have houtW : ∃ z, z ∉ W := by
      by_contra hh
      push Not at hh
      exact hnW (Set.eq_univ_of_forall hh)
    obtain ⟨z, hz⟩ := houtW
    refine ⟨z, ?_⟩
    intro hzc
    simp only [c, SimpleGraph.Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzq
    · exact hz (hperm.mem_iff.mp q.end_mem_support)
    · exact hz (hperm.mem_iff.mp hzq)
  obtain ⟨u, v, R, hR, hRlen⟩ := extend_nonspanning_cycle hconn c hc hout
  have hh := hmax u v R hR
  simp only [c, SimpleGraph.Walk.length_cons, hqlen] at hRlen
  omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_DenseCycles
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem cycle_from_dense_layer {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 8 ≤ k) {r : V} {i : ℕ} (hi : i ≤ k / 2)
    {S : Set V} (hSD : S ⊆ distanceLayer G r i) (hS : S.Nonempty)
    (hdense : MinimalDensity (G.induce S) (k / 2) (k % 2))
    (hfree : ¬ (⊤ : SimpleGraph (Fin (k / 2))) ⊑ G) :
    SimpleGraph.cycleGraph (k + 1) ⊑ G := by
  classical
  let : Nonempty S := hS.to_subtype
  let H := G.induce S
  let f : H ↪g G := SimpleGraph.Embedding.induce S
  have hfreeH : ¬ (⊤ : SimpleGraph (Fin (k / 2))) ⊑ H :=
    fun hh => hfree (hh.trans f.isContained)
  obtain ⟨hconn, hnb, horder, hdegree, hexp⟩ :=
    minimal_density_properties (by omega : 4 ≤ k / 2) (by omega : k % 2 ≤ 1) hdense hfreeH
  have horder' : k ≤ Fintype.card S := by omega
  obtain ⟨B⟩ := exists_breadthFirstParent G r
  have hneS : ∃ x ∈ S, ∃ y ∈ S, x ≠ y :=
    (Set.one_lt_ncard).mp (by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      omega)
  obtain ⟨d, hd, c, hc, x, hx, z, hz, hxz⟩ := exists_layer_split B hSD hneS
  let ℓ := k + 1 - 2 * (i - d)
  have hℓpos : 1 ≤ ℓ := by dsimp [ℓ]; omega
  have hpair : ∀ a b : S, a ≠ b → ¬ H.Adj a b →
      2 * (k / 2) ≤ (closedNeighborhood H {a, b}).ncard := by
    intro a b hab hnadj
    have hI : H.IsIndepSet {a, b} := by
      intro x hx y hy hxy hxyadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hnadj hxyadj
      · exact hnadj hxyadj.symm
      · exact hxy rfl
    have he := (hexp {a, b} hI (Set.insert_nonempty _ _)).1
    simpa only [Set.ncard_pair hab, Nat.mul_comm] using he
  have hchoose : ∃ y z : S, layerAncestor B i y.val (d + 1) ≠
      layerAncestor B i z.val (d + 1) ∧ ∃ p : H.Walk y z, p.IsPath ∧ p.length = ℓ := by
    by_cases hdepth : i - d = 1
    · obtain ⟨y, z, p, hp, hlong⟩ := long_path_min_degree
        (by omega : 2 ≤ k / 2) hconn hdegree
      have hlen : ℓ ≤ p.length := by dsimp [ℓ] at *; omega
      have htake := hp.take ℓ
      have htlen : (p.take ℓ).length = ℓ := by rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hlen]
      refine ⟨y, p.getVert ℓ, ?_, p.take ℓ, htake, htlen⟩
      have he : d + 1 = i := by omega
      simp only [he, layerAncestor_self]
      intro heq
      have hn := (htake.nil_iff_eq).mpr (Subtype.ext heq)
      have hh := hn.length_eq_zero
      omega
    · let χ : S → Fin 2 := fun v =>
        if layerAncestor B i v.val (d + 1) = layerAncestor B i x (d + 1) then 0 else 1
      have hχ : ∃ y z, χ y ≠ χ z := by
        refine ⟨⟨x, hx⟩, ⟨z, hz⟩, ?_⟩
        simp [χ, Ne.symm hxz]
      have hℓmax : ℓ ≤ 2 * (k / 2) - 2 := by dsimp [ℓ]; omega
      obtain ⟨y, z, hyz, p, hp, hlen⟩ := coloured_path H (k / 2) (by omega)
        hconn hnb hfreeH hdegree hpair χ hχ ℓ hℓpos hℓmax
      refine ⟨y, z, ?_, p, hp, hlen⟩
      intro heq
      apply hyz
      simp only [χ, heq]
  obtain ⟨y, z, hbranch, p, hp, hlen⟩ := hchoose
  have hcommon : layerAncestor B i y.val d = layerAncestor B i z.val d :=
    (hc y.val y.property).trans (hc z.val z.property).symm
  obtain ⟨q, hq, hqlen, hqint⟩ := exists_branch_path B (hSD y.property) (hSD z.property)
    hd hcommon hbranch
  let inc : H →g G := ⟨Subtype.val, fun ha => ha⟩
  let P : G.Walk y.val z.val := p.map inc
  have hP : P.IsPath := hp.map Subtype.val_injective
  have hplay : ∀ w ∈ P.support, G.dist r w = i := by
    intro w hw
    rw [SimpleGraph.Walk.support_map] at hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    exact (hSD v.property).2
  have hcyc := cycle_of_layer_path P hP hplay q hq (by rw [hqlen]; omega) hqint
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < k + 1)).mpr
  refine ⟨y.val, P.append q.reverse, hcyc, ?_⟩
  dsimp only [P]
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.length_map, hlen, hqlen]
  dsimp [ℓ]
  omega

 
theorem contains_half_clique {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} (hk : 8 ≤ k) (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) :
    (⊤ : SimpleGraph (Fin (k / 2))) ⊑ G := by
  by_contra hfree
  obtain ⟨r⟩ := ‹Nonempty V›
  obtain ⟨i, _, hi, S, hSD, hS, hdense⟩ := exists_minimal_dense_layer hk hα hexp r
  exact hcycle (cycle_from_dense_layer hk hi hSD hS hdense hfree)

 

theorem triangle_free_card_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (a : ℕ) (hfree : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G) (hα : G.indepNum ≤ a) :
    2 * Fintype.card V ≤ a * (a + 3) := by
  classical
  induction a generalizing V with
  | zero =>
    have hempty : IsEmpty V := ⟨fun v => by
      have hI : G.IsIndepSet {v} := Set.pairwise_singleton _ _
      have hc := (indep_ncard_le hI).trans hα
      simp at hc⟩
    let := hempty
    simp
  | succ a ih =>
    cases isEmpty_or_nonempty V with
    | inl he => let := he; simp
    | inr he =>
      let := he
      obtain ⟨v⟩ := he
      have hNind : G.IsIndepSet (G.neighborSet v) :=
        (SimpleGraph.isClique_compl G).mp (neighborhood_compl_clique_of_triangle_free hfree v)
      have hNcard := (indep_ncard_le hNind).trans hα
      let N := closedNeighborhood G {v}
      let R := Nᶜ
      have hNc : N.ncard ≤ a + 2 := by
        dsimp [N]
        rw [closedNeighborhood_singleton_card]
        rw [ncard_neighborSet] at hNcard
        omega
      have hαR : (G.induce R).indepNum ≤ a := by
        have hh := independence_outside_closed
          (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.subset_univ {v})
        rw [independence_univ, Set.ncard_singleton, ← Set.compl_eq_univ_sdiff] at hh
        change independence G R + 1 ≤ G.indepNum at hh
        change independence G R ≤ a
        omega
      have hfreeR : ¬ (⊤ : SimpleGraph (Fin 3)) ⊑ G.induce R :=
        fun h => hfree (h.trans (SimpleGraph.Embedding.induce R).isContained)
      have hcR := ih (G.induce R) hfreeR hαR
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hcR
      have hsum := Set.ncard_add_ncard_compl N
      rw [Nat.card_eq_fintype_card] at hsum
      change 2 * R.ncard ≤ a * (a + 3) at hcR
      nlinarith

 
theorem counterexample_contains_triangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (_ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k * a + 1) (hα : G.indepNum ≤ a) :
    (⊤ : SimpleGraph (Fin 3)) ⊑ G := by
  by_contra hfree
  have hh := triangle_free_card_bound G a hfree hα
  rw [horder] at hh
  have hcomp : a + 3 ≤ 2 * k := by omega
  have hm := Nat.mul_le_mul_left a hcomp
  nlinarith

 
theorem complete_isContained_iff_le_cliqueNum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) :
    (⊤ : SimpleGraph (Fin t)) ⊑ G ↔ t ≤ G.cliqueNum := by
  classical
  constructor
  · intro ht
    have hn := ht.not_cliqueFree
    simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hn
    obtain ⟨Q, hQ⟩ := hn
    have hh := hQ.isClique.card_le_cliqueNum
    rwa [hQ.card_eq] at hh
  · intro ht
    by_contra hn
    obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
    have hh := clique_ncard_lt hn hQ.isClique
    rw [Set.ncard_coe_finset, hQ.card_eq] at hh
    omega

 
theorem counterexample_clique_bound {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k * a + 1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  have hthree := (complete_isContained_iff_le_cliqueNum G 3).mp
    (counterexample_contains_triangle hk ha hak horder hα)
  refine ⟨max_le hthree ?_, ?_⟩
  · by_cases hlarge : 8 ≤ k
    · let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      exact (complete_isContained_iff_le_cliqueNum G _).mp
        (contains_half_clique hlarge (hα.trans hak) hexp hcycle)
    · omega
  · by_contra hn
    have htop := (complete_isContained_iff_le_cliqueNum G (k + 1)).mpr (by omega)
    exact hcycle ((SimpleGraph.IsContained.of_le (show SimpleGraph.cycleGraph (k + 1) ≤ ⊤
      from le_top)).trans htop)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_IndependenceTwo
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem alpha_two_adj {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hx : ¬ G.Adj x z) (hy : ¬ G.Adj y z) : G.Adj x y := by
  classical
  by_contra hxyadj
  have hI : G.IsIndepSet {x, y, z} := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact hxyadj
    · exact hx
    · exact fun h => hxyadj h.symm
    · exact (hab rfl).elim
    · exact hy
    · exact fun h => hx h.symm
    · exact fun h => hy h.symm
    · exact (hab rfl).elim
  have hc := (indep_ncard_le hI).trans hα
  simp [Set.ncard_insert_of_notMem, hxy, hxz, hyz] at hc

theorem clique_ncard_le_cliqueNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hS : G.IsClique S) : S.ncard ≤ G.cliqueNum := by
  classical
  have hh : G.IsClique (S.toFinset : Set V) := by simpa using hS
  simpa only [Set.ncard_eq_toFinset_card'] using hh.card_le_cliqueNum

 
theorem clique_of_anticomplete_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {S : Set V} {z : V} (hz : z ∉ S)
    (hanti : ∀ x ∈ S, ¬ G.Adj x z) : G.IsClique S := by
  intro x hx y hy hxy
  exact alpha_two_adj hα (z := z) hxy (fun he => hz (he ▸ hx))
    (fun he => hz (he ▸ hy)) (hanti x hx) (hanti y hy)

 
theorem connected_of_alpha_two_large {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (hα : G.indepNum ≤ 2) (ht : G.cliqueNum ≤ t)
    (hcard : 2 * t < Fintype.card V) : G.Connected := by
  classical
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let := hne
  refine ⟨?_⟩
  intro x y
  by_contra hxy
  let S := {v | G.Reachable x v}
  have hx : x ∈ S := SimpleGraph.Reachable.rfl
  have hy : y ∉ S := hxy
  have hanti : ∀ a ∈ S, ∀ b ∈ Sᶜ, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb (ha.trans hab.reachable)
  have hS : G.IsClique S := clique_of_anticomplete_vertex hα hy (fun a ha => hanti a ha y hy)
  have hR : G.IsClique Sᶜ := clique_of_anticomplete_vertex hα
    (show x ∉ Sᶜ from fun hh => hh hx) (fun b hb hab => hanti x hx b hb hab.symm)
  have hcS := (clique_ncard_le_cliqueNum hS).trans ht
  have hcR := (clique_ncard_le_cliqueNum hR).trans ht
  have hsum := Set.ncard_add_ncard_compl S
  rw [Nat.card_eq_fintype_card] at hsum
  omega

 

theorem deletion_connected_of_alpha_two_large {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hα : G.indepNum ≤ 2) (ht : G.cliqueNum ≤ t)
    (hcard : 2 * t < Fintype.card V) (v x y : V) (hxv : x ≠ v) (hyv : y ≠ v) :
    (within G {w | w ≠ v}).Reachable x y := by
  classical
  let D := within G {w | w ≠ v}
  by_contra hxy
  let A : Set V := {w | D.Reachable x w}
  let B : Set V := {w | w ≠ v} \ A
  have hxA : x ∈ A := SimpleGraph.Reachable.rfl
  have hAv : ∀ a ∈ A, a ≠ v := by
    rintro a ⟨p⟩
    exact within_support p hxv a p.end_mem_support
  have hyB : y ∈ B := ⟨hyv, hxy⟩
  have hanti : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb.2 (ha.trans (show D.Adj a b from ⟨hab, hAv a ha, hb.1⟩).reachable)
  have hA : G.IsClique A := clique_of_anticomplete_vertex hα hyB.2
    (fun a ha => hanti a ha y hyB)
  have hB : G.IsClique B := clique_of_anticomplete_vertex hα
    (show x ∉ B from fun hh => hh.2 hxA) (fun b hb hab => hanti x hxA b hb hab.symm)
  have hcA := (clique_ncard_le_cliqueNum hA).trans ht
  have hcB := (clique_ncard_le_cliqueNum hB).trans ht
  have hvAB : v ∉ A ∪ B := by
    rintro (ha | hb)
    · exact hAv v ha rfl
    · exact hb.1 rfl
  have huniv : insert v (A ∪ B) = Set.univ := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_univ, iff_true]
    by_cases hwv : w = v
    · exact Or.inl hwv
    · by_cases hw : w ∈ A
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr ⟨hwv, hw⟩)
  have hdis : Disjoint A B := Set.disjoint_left.mpr (fun a ha hb => hb.2 ha)
  have hsum : A.ncard + B.ncard + 1 = Fintype.card V := by
    have hh := congrArg Set.ncard huniv
    simpa only [Set.ncard_insert_of_notMem hvAB, Set.ncard_union_eq hdis,
      Set.ncard_univ, Nat.card_eq_fintype_card] using hh
  have hAc : A.ncard = t := by omega
  have hBc : B.ncard = t := by omega
  have hone : (∀ a ∈ A, G.Adj v a) ∨ (∀ b ∈ B, G.Adj v b) := by
    by_cases ha : ∀ a ∈ A, G.Adj v a
    · exact Or.inl ha
    · push Not at ha
      obtain ⟨a, ha, hva⟩ := ha
      refine Or.inr (fun b hb => ?_)
      exact alpha_two_adj hα (Ne.symm hb.1) (Ne.symm (hAv a ha))
        (fun he => hb.2 (he ▸ ha)) hva (fun h => hanti a ha b hb h.symm)
  rcases hone with ha | hb
  · have hcl : G.IsClique (insert v A) := hA.insert (fun a ha' _ => ha a ha')
    have hc := (clique_ncard_le_cliqueNum hcl).trans ht
    rw [Set.ncard_insert_of_notMem (fun hv => hAv v hv rfl), hAc] at hc
    omega
  · have hcl : G.IsClique (insert v B) := hB.insert (fun b hb' _ => hb b hb')
    have hc := (clique_ncard_le_cliqueNum hcl).trans ht
    rw [Set.ncard_insert_of_notMem (fun hv => hv.1 rfl), hBc] at hc
    omega

 

theorem degree_two_of_deletion_connected {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hdel : ∀ v x y, x ≠ v → y ≠ v → (within G {w | w ≠ v}).Reachable x y)
    (x : V) : 2 ≤ G.degree x := by
  classical
  obtain ⟨y, _, hyx⟩ := exists_mem_ne_of_ncard (E := Set.univ) (w₀ := x)
    (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using (by omega : 2 ≤ Fintype.card V))
  obtain ⟨p⟩ := hconn.preconnected x y
  have hplen : 0 < p.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hyx hn.eq.symm)
  let w := p.getVert 1
  have hxw : G.Adj x w := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add]
      using (p.adj_getVert_succ (i := 0) hplen)
  have hex : ∃ z : V, z ≠ x ∧ z ≠ w := by
    by_contra hn
    push Not at hn
    have hsub : (Set.univ : Set V) ⊆ {x, w} := by
      intro z _
      by_cases hz : z = x
      · exact Or.inl hz
      · exact Or.inr (hn z hz)
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Set.ncard_pair hxw.ne] at hh
    omega
  obtain ⟨z, hzx, hzw⟩ := hex
  obtain ⟨q⟩ := hdel w x z hxw.ne hzw
  have hqlen : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hzx hn.eq.symm)
  let u := q.getVert 1
  have hxu : (within G {a | a ≠ w}).Adj x u := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add]
      using q.adj_getVert_succ (i := 0) hqlen
  have hh : 1 < (G.neighborSet x).ncard := (Set.one_lt_ncard).mpr
    ⟨w, hxw, u, hxu.1, Ne.symm hxu.2.2⟩
  rw [ncard_neighborSet] at hh
  omega

 

theorem hamiltonian_of_alpha_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) (hα : G.indepNum ≤ 2)
    (hdel : ∀ v x y, x ≠ v → y ≠ v → (within G {w | w ≠ v}).Reachable x y) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ c.length = Fintype.card V := by
  classical
  let : Nonempty V := hconn.nonempty
  have hdegree := degree_two_of_deletion_connected hconn hcard hdel
  obtain ⟨x, y, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  obtain ⟨a, b, P, hP, hPlen⟩ := long_path_min_degree (by omega : 2 ≤ 2) hconn hdegree
  have hlen : 2 ≤ p.length := by
    have hh := hmax a b P hP
    omega
  have hW : 1 < p.support.length := by rw [SimpleGraph.Walk.length_support]; omega
  have hyN : ∀ z, G.Adj y z → z ∈ p.support :=
    longest_path_endpoint_neighbors p hp (fun z q hq => hmax x z q hq)
  have hxN : ∀ z, G.Adj x z → z ∈ p.support := by
    intro z hxz
    have hh := longest_path_endpoint_neighbors p.reverse hp.reverse
      (fun z q hq => by simpa using hmax y z q hq) z hxz
    simpa using hh
  have hspan : ∀ z, z ∈ p.support := by
    intro z
    by_contra hz
    have hxy : x ≠ y := by
      intro hh
      have hn := (hp.nil_iff_eq).mpr hh
      have hh := hn.length_eq_zero
      omega
    have hxyadj := alpha_two_adj hα (z := z) hxy
      (fun hh => hz (by rw [← hh]; exact p.start_mem_support))
      (fun hh => hz (by rw [← hh]; exact p.end_mem_support))
      (fun hh => hz (hxN z hh)) (fun hh => hz (hyN z hh))
    let c := SimpleGraph.Walk.cons hxyadj.symm p
    have hc : c.IsCycle := path_close_cycle p hp hlen hxyadj.symm
    have hzc : z ∉ c.support := by
      simp only [c, SimpleGraph.Walk.support_cons, List.mem_cons]
      exact fun hh => hh.elim (fun hh => hz (by rw [hh]; exact p.end_mem_support)) hz
    obtain ⟨u, v, q, hq, hqlen⟩ := extend_nonspanning_cycle hconn c hc ⟨z, hzc⟩
    have hh := hmax u v q hq
    simp only [c, SimpleGraph.Walk.length_cons] at hqlen
    omega
  have hcardp : p.length + 1 = Fintype.card V := by
    have hh : p.support.toFinset = Finset.univ := by ext z; simp [hspan]
    have hc := congrArg Finset.card hh
    simpa only [List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support, Finset.card_univ] using hc
  let E := pathEnds G x p.support
  have hxE : x ∉ E := pathEnds_no_start hW
  have hyE : y ∈ E := ⟨p, hp, .refl _⟩
  have hEc : 2 ≤ E.ncard :=
    (hdegree y).trans (degree_le_card_pathEnds p hp (.refl _) hyN)
  have hclose : ∃ e ∈ E, G.Adj x e := by
    by_contra hn
    push Not at hn
    have hcl : G.IsClique E := clique_of_anticomplete_vertex hα hxE
      (fun e he he' => hn e he he'.symm)
    obtain ⟨j, hjpos, hjlen, hseg⟩ := pathEnds_final_segment p hp (.refl _) hcl hW
    have hjtwo : 2 ≤ j := by
      by_contra hh
      have hjone : j = 1 := by omega
      have hfirst := p.adj_getVert_succ (i := 0) (by omega)
      simp only [SimpleGraph.Walk.getVert_zero, zero_add] at hfirst
      exact hn (p.getVert 1) ((hseg 1 (by omega)).mpr (by omega)) hfirst
    let u := p.getVert (j - 1)
    let w₀ := p.getVert j
    have huE : u ∉ E := by
      exact fun hu => by have hh := (hseg (j - 1) (by omega)).mp hu; omega
    have hxw : x ≠ w₀ := by
      intro hh
      exact hxE (hh ▸ (hseg j hjlen).mpr le_rfl)
    have hux : u ≠ x := by
      intro hh
      have hh' := (hp.getVert_eq_start_iff (show j - 1 ≤ p.length by omega)).mp hh
      omega
    obtain ⟨w₁, hw₁, hw₁ne⟩ := exists_mem_ne_of_ncard (w₀ := w₀) hEc
    obtain ⟨q⟩ := hdel w₀ x w₁ hxw hw₁ne
    obtain ⟨d, hd, hdout, hdin⟩ := q.exists_boundary_dart Eᶜ hxE
      (show w₁ ∉ Eᶜ from fun hh => hh hw₁)
    have hdinE : d.snd ∈ E := not_not.mp hdin
    have hdinne : d.snd ≠ w₀ := d.adj.2.2
    have hpartial := pathEnds_partial_attachment p hp (fun v q hq => hmax x v q hq)
      hcl hjpos hjlen hseg hdinE hdinne d.fst d.adj.1.symm
    have hdu : d.fst = u := hpartial.resolve_left hdout
    have hentry : G.Adj u d.snd := hdu ▸ d.adj.1
    have hattach := pathEnds_attachment_of_two_entries p hp (fun v q hq => hmax x v q hq)
      hcl hjpos hjlen hseg hdinE hdinne hentry
    have hyu : y ≠ u := fun hh => huE (hh ▸ hyE)
    obtain ⟨q'⟩ := hdel u x y hux.symm hyu
    obtain ⟨d', _, hd'out, hd'in⟩ := q'.exists_boundary_dart Eᶜ hxE
      (show y ∉ Eᶜ from fun hh => hh hyE)
    have hlast := hattach d'.snd (not_not.mp hd'in) d'.fst d'.adj.1.symm
    exact d'.adj.2.1 (hlast.resolve_left hd'out)
  obtain ⟨e, he, hxe⟩ := hclose
  obtain ⟨q, hq, hperm⟩ := he
  have hqlen : q.length = p.length := by
    have hh := hperm.length_eq
    simp only [SimpleGraph.Walk.length_support] at hh
    omega
  refine ⟨e, .cons hxe.symm q, path_close_cycle q hq (by omega) hxe.symm, ?_⟩
  simpa only [SimpleGraph.Walk.length_cons, hqlen] using hcardp

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CycleShortening
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem cycleGraph_adj_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) {a b : Fin n} :
    (SimpleGraph.cycleGraph n).Adj a b ↔ a = b + 1 ∨ b = a + 1 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  simp only [add_comm]

theorem contains_cycle_of_labels {V : Type*} {G : SimpleGraph V}
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (f : Fin n → V) (hf : Function.Injective f)
    (hstep : ∀ i, G.Adj (f i) (f (i + 1))) : SimpleGraph.cycleGraph n ⊑ G := by
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro a b hab
  rcases (cycleGraph_adj_succ hn).mp hab with rfl | rfl
  · exact (hstep b).symm
  · exact hstep a

theorem fin_add_one_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (i + 1).val = if i.val + 1 = n then 0 else i.val + 1 := by
  simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  split_ifs with h
  · simp [h]
  · rw [Nat.mod_eq_of_lt (by omega)]


theorem bypassIndex_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (bypassIndex hn) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  simp only [bypassIndex] at hh
  apply Fin.ext
  split_ifs at hh <;> omega

theorem bypassIndex_step {n : ℕ} [NeZero n] [NeZero (n - 1)] (hn : 3 ≤ n)
    (i : Fin (n - 1)) :
    (bypassIndex hn i = 0 ∧ bypassIndex hn (i + 1) = 2) ∨
      bypassIndex hn (i + 1) = bypassIndex hn i + 1 := by
  have hval := fin_add_one_val (by omega : 2 ≤ n - 1) i
  by_cases hi : i.val = 0
  · left
    constructor <;> apply Fin.ext
    · simp [bypassIndex, hi]
    · have hi1 : (i + 1).val = 1 := by rw [hval]; split_ifs <;> omega
      simp [bypassIndex, hi1, Nat.mod_eq_of_lt (by omega : 2 < n)]
  · right
    apply Fin.ext
    rw [fin_add_one_val (by omega) (bypassIndex hn i)]
    simp only [bypassIndex]
    rw [hval]
    split_ifs <;> omega


theorem fourStepIndex_injective {n : ℕ} (hn : 7 ≤ n) :
    Function.Injective (fourStepIndex hn) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  simp only [fourStepIndex] at hh
  apply Fin.ext
  split_ifs at hh <;> omega

theorem fourStepIndex_step {n : ℕ} [NeZero n] [NeZero (n - 1)] (hn : 7 ≤ n)
    (i : Fin (n - 1)) :
    fourStepIndex hn (i + 1) = fourStepIndex hn i + 1 ∨
      fourStepIndex hn (i + 1) = fourStepIndex hn i + 4 ∨
      fourStepIndex hn i = fourStepIndex hn (i + 1) + 4 := by
  have hval := fin_add_one_val (by omega : 2 ≤ n - 1) i
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h4 : 4 % n = 4 := Nat.mod_eq_of_lt (by omega)
  have h1' : (1 : Fin n).val = 1 := by rw [Fin.val_one', h1]
  have h4' : (4 : Fin n).val = 4 := h4
  simp only [Fin.ext_iff, Fin.val_add, h1', h4', fourStepIndex, hval]
  split_ifs <;> simp_all only [ite_false, if_false, ite_true, if_true]
  all_goals first
    | (left; rw [Nat.mod_eq_of_lt (by omega)] <;> omega)
    | (right; left; rw [Nat.mod_eq_of_lt (by omega)])
    | (right; right; rw [Nat.mod_eq_of_lt (by omega)]; omega)
    | (right; left; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)

 
theorem fin_ne_add_step {n : ℕ} [NeZero n] (i : Fin n) (d : ℕ)
    (hd : 0 < d) (hdn : d < n) : i ≠ i + Fin.ofNat n d := by
  intro he
  have hh : (0 : Fin n) = Fin.ofNat n d := add_left_cancel (show i + 0 = i + Fin.ofNat n d by
    simpa only [add_zero] using he)
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero, Fin.val_ofNat, Nat.mod_eq_of_lt hdn] at hv
  omega

 

theorem shorten_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {n : ℕ} (hn : 7 ≤ n)
    (hc : SimpleGraph.cycleGraph n ⊑ G) : SimpleGraph.cycleGraph (n - 1) ⊑ G := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : NeZero (n - 1) := ⟨by omega⟩
  obtain ⟨f⟩ := hc
  have h22 : (2 : Fin n) + 2 = 4 := by
    apply Fin.ext
    change (2 % n + 2 % n) % n = 4 % n
    simp only [Nat.mod_eq_of_lt (by omega : 2 < n)]
  have hstep : ∀ i : Fin n, G.Adj (f i) (f (i + 1)) := by
    intro i
    exact f.toHom.map_adj ((cycleGraph_adj_succ (by omega)).mpr (Or.inr rfl))
  by_cases hchord : ∃ i : Fin n, G.Adj (f i) (f (i + 2))
  · obtain ⟨i, hi⟩ := hchord
    let g : Fin (n - 1) → V := fun j => f (i + bypassIndex (by omega : 3 ≤ n) j)
    apply contains_cycle_of_labels (by omega) g
    · intro a b hab
      exact bypassIndex_injective (by omega) (add_left_cancel (f.injective hab))
    · intro j
      rcases bypassIndex_step (by omega : 3 ≤ n) j with ⟨hj, hj'⟩ | hj
      · simpa only [g, hj, hj', add_zero] using hi
      · simpa only [g, hj, ← add_assoc] using hstep (i + bypassIndex (by omega) j)
  · push Not at hchord
    have hfour : ∀ i : Fin n, G.Adj (f i) (f (i + 4)) := by
      intro i
      have h02 : i ≠ i + 2 := fin_ne_add_step i 2 (by omega) (by omega)
      have h04 : i ≠ i + 4 := fin_ne_add_step i 4 (by omega) (by omega)
      have h24 : i + 2 ≠ i + 4 := by
        have hn24 := fin_ne_add_step (i + 2) 2 (by omega) (by omega)
        change i + 2 ≠ i + 2 + 2 at hn24
        simpa only [add_assoc, h22] using hn24
      apply alpha_two_adj hα (z := f (i + 2))
      · exact fun hh => h04 (f.injective hh)
      · exact fun hh => h02 (f.injective hh)
      · exact fun hh => h24 (f.injective hh).symm
      · exact hchord i
      · intro hh
        apply hchord (i + 2)
        simpa only [add_assoc, h22] using hh.symm
    apply contains_cycle_of_labels (by omega) (fun j => f (fourStepIndex hn j))
    · exact f.injective.comp (fourStepIndex_injective hn)
    · intro j
      rcases fourStepIndex_step hn j with hj | hj | hj
      · rw [hj]; exact hstep _
      · rw [hj]; exact hfour _
      · rw [hj]; exact (hfour _).symm

 
theorem cycle_of_alpha_two_long_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {k : ℕ} (hk : 6 ≤ k) :
    ∀ n, k ≤ n → SimpleGraph.cycleGraph n ⊑ G → SimpleGraph.cycleGraph k ⊑ G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hkn hc
    by_cases he : k = n
    · rw [he]; exact hc
    · exact ih (n - 1) (by omega) (by omega) (shorten_cycle hα (by omega) hc)

 
theorem size_test {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k t : ℕ} (hk : 5 ≤ k) (_ht : 1 ≤ t)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hclique : G.cliqueNum ≤ t)
    (Y : Set V) (hY : max k (2 * t) < Y.ncard) : 3 ≤ independence G Y := by
  classical
  by_contra hn
  have hα : (G.induce Y).indepNum ≤ 2 := by change independence G Y ≤ 2; omega
  have hcY : (G.induce Y).cliqueNum ≤ t := by
    by_contra hh
    have hc := (complete_isContained_iff_le_cliqueNum (G.induce Y) (t + 1)).mpr (by omega)
    have hc' := (complete_isContained_iff_le_cliqueNum G (t + 1)).mp
      (hc.trans (SimpleGraph.Embedding.induce Y).isContained)
    omega
  have hcard : max k (2 * t) < Fintype.card Y := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hconn := connected_of_alpha_two_large hα hcY (by omega)
  have hdel := deletion_connected_of_alpha_two_large hα hcY (by omega)
  obtain ⟨x, c, hc, hlen⟩ := hamiltonian_of_alpha_two hconn (by omega) hα hdel
  have hlong : SimpleGraph.cycleGraph (Fintype.card Y) ⊑ G.induce Y :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr ⟨x, c, hc, hlen⟩
  have hshort := cycle_of_alpha_two_long_cycle hα (by omega : 6 ≤ k + 1)
    (Fintype.card Y) (by omega) hlong
  exact hcycle (hshort.trans (SimpleGraph.Embedding.induce Y).isContained)



end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ExteriorPaths
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem exteriorEdges_le {V : Type*} (G : SimpleGraph V) (X : Set V) :
    exteriorEdges G X ≤ G := fun _ _ h => h.1


theorem outsideBall_subset_compl {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) : outsideBall G X x r ⊆ Xᶜ := by
  cases r <;> exact fun _ h => h.2

theorem outsideBall_subset_succ {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) : outsideBall G X x r ⊆ outsideBall G X x (r + 1) :=
  fun _ h => ⟨Or.inl h, outsideBall_subset_compl G X x r h⟩

theorem closedNeighborhood_ball_subset {V : Type*} (G : SimpleGraph V) (X : Set V)
    (x : V) (r : ℕ) :
    closedNeighborhood G (outsideBall G X x r) ⊆ outsideBall G X x (r + 1) ∪ X := by
  intro v hv
  by_cases hx : v ∈ X
  · exact Or.inr hx
  · exact Or.inl ⟨hv, hx⟩

 

theorem outsideBall_walk {V : Type*} {G : SimpleGraph V} {X : Set V} {x z : V}
    {r : ℕ} (hz : z ∈ outsideBall G X x r) :
    ∃ p : (exteriorEdges G X).Walk x z, p.length ≤ r + 1 ∧
      ∀ v ∈ p.support, v = x ∨ v ∉ X := by
  induction r generalizing z with
  | zero =>
    change G.Adj x z ∧ z ∉ X at hz
    let p : (exteriorEdges G X).Walk x z := .cons ⟨hz.1, Or.inr hz.2⟩ .nil
    refine ⟨p, by change 1 ≤ 1; omega, ?_⟩
    dsimp [p]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hz.2
  | succ r ih =>
    change (z ∈ outsideBall G X x r ∨ ∃ u ∈ outsideBall G X x r, G.Adj u z) ∧ z ∉ X at hz
    rcases hz.1 with hold | ⟨u, hu, huz⟩
    · obtain ⟨p, hp, hs⟩ := ih hold
      exact ⟨p, by omega, hs⟩
    · obtain ⟨p, hp, hs⟩ := ih hu
      refine ⟨p.concat ⟨huz, Or.inr hz.2⟩, ?_, ?_⟩
      · rw [SimpleGraph.Walk.length_concat]
        omega
      · intro v hv
        simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hs v hv
        · exact Or.inr hz.2

 

theorem outsidePath_of_exterior_walk {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (p : (exteriorEdges G X).Walk x y)
    (hs : ∀ v ∈ p.support, v ∈ X → v = x ∨ v = y) :
    ∃ d, 1 ≤ d ∧ d + 1 ≤ p.length ∧ OutsidePath G X x y d := by
  classical
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp
    (fun hn => hxy hn.eq)
  have htwo : 2 ≤ q.length := by
    by_contra hn
    have hh := q.adj_of_length_eq_one (by omega)
    exact hh.2.elim (fun hn => hn hx) (fun hn => hn hy)
  refine ⟨q.length - 1, by omega, ?_, hx, hy, hxy,
    q.mapLe (exteriorEdges_le G X), hq.mapLe _, ?_, ?_⟩
  · have hh := p.length_bypass_le_length; dsimp [q] at *; omega
  · simp only [SimpleGraph.Walk.length_mapLe]; omega
  · intro v hv hvX
    have hvq : v ∈ q.support := by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hv
    exact hs v (p.support_bypass_subset_support hvq) hvX

 
theorem outsidePath_of_balls_meet {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hzx : z ∈ outsideBall G X x r) (hzy : z ∈ outsideBall G X y s) :
    ∃ d, 1 ≤ d ∧ d ≤ r + s + 1 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hzx
  obtain ⟨q, hq, hqs⟩ := outsideBall_walk hzy
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy (p.append q.reverse) (by
    intro v hv hvX
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
    · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
  refine ⟨d, hd, ?_, hout⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hlen
  omega

 
theorem outsidePath_of_balls_adj {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z w : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hz : z ∈ outsideBall G X x r) (hw : w ∈ outsideBall G X y s) (hzw : G.Adj z w) :
    ∃ d, 1 ≤ d ∧ d ≤ r + s + 2 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hz
  obtain ⟨q, hq, hqs⟩ := outsideBall_walk hw
  let P := (p.concat ⟨hzw, Or.inl (outsideBall_subset_compl G X x r hz)⟩).append q.reverse
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy P (by
    intro v hv hvX
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
      · exact (outsideBall_subset_compl G X y s hw hvX).elim
    · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
  refine ⟨d, hd, ?_, hout⟩
  dsimp [P] at hlen
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hlen
  rw [SimpleGraph.Walk.length_concat] at hlen
  omega

theorem outside_balls_separated {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} {r s : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hno : ∀ d, 1 ≤ d → d ≤ r + s + 2 → ¬ OutsidePath G X x y d) :
    Disjoint (outsideBall G X x r) (outsideBall G X y s) ∧
      ∀ z ∈ outsideBall G X x r, ∀ w ∈ outsideBall G X y s, ¬ G.Adj z w := by
  constructor
  · apply Set.disjoint_left.mpr
    intro z hzx hzy
    obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_balls_meet hx hy hxy hzx hzy
    exact hno d hd (by omega) hp
  · intro z hz w hw hzw
    obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_balls_adj hx hy hxy hz hw hzw
    exact hno d hd hd' hp

 
theorem outsidePath_of_ball_adj {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y z : V} {r : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hz : z ∈ outsideBall G X x r) (hzy : G.Adj z y) :
    ∃ d, 1 ≤ d ∧ d ≤ r + 1 ∧ OutsidePath G X x y d := by
  obtain ⟨p, hp, hps⟩ := outsideBall_walk hz
  obtain ⟨d, hd, hlen, hout⟩ := outsidePath_of_exterior_walk hx hy hxy
    (p.concat ⟨hzy, Or.inl (outsideBall_subset_compl G X x r hz)⟩) (by
      intro v hv hvX
      simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
      · exact Or.inr rfl)
  refine ⟨d, hd, ?_, hout⟩
  rw [SimpleGraph.Walk.length_concat] at hlen
  omega

theorem outside_ball_misses {V : Type*} {G : SimpleGraph V} {X : Set V}
    {x y : V} {r : ℕ} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y)
    (hno : ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ OutsidePath G X x y d) :
    ∀ z ∈ outsideBall G X x r, ¬ G.Adj z y := by
  intro z hz hzy
  obtain ⟨d, hd, hd', hp⟩ := outsidePath_of_ball_adj hx hy hxy hz hzy
  exact hno d hd hd' hp

attribute [local instance] Classical.propDecidable

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_PathSystems
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable



theorem clique_chains_flatten {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (hQ : G.IsClique Q) (C : List (List V)) (hne : [] ∉ C)
    (hnd : C.flatten.Nodup) (hedges : ∀ c ∈ C, c.IsChain G.Adj)
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q)) :
    C.flatten.IsChain G.Adj := by
  apply (List.isChain_flatten hne).mpr
  refine ⟨hedges, ?_⟩
  apply List.Pairwise.isChain
  apply (List.nodup_flatten.mp hnd).2.imp_of_mem
  intro a b ha hb hab x hx y hy
  apply hQ ((hends a ha).2 x hx) ((hends b hb).1 y hy)
  intro hxy
  exact List.disjoint_left.mp hab (List.mem_of_mem_getLast? hx)
    (hxy ▸ List.mem_of_mem_head? hy)

theorem clique_chains_endpoints {V : Type*} {Q : Set V} (C : List (List V))
    (hne : ∀ c ∈ C, c ≠ [])
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q))
    (hf : C.flatten ≠ []) :
    C.flatten.head hf ∈ Q ∧ C.flatten.getLast hf ∈ Q := by
  have hc : C ≠ [] := by intro h; simp [h] at hf
  constructor
  · rw [List.head_flatten_eq_head_head hf (hne _ (List.head_mem hc))]
    apply (hends _ (List.head_mem hc)).1
    exact List.head?_eq_some_head (hne _ (List.head_mem hc))
  · rw [List.getLast_flatten_eq_getLast_getLast hf (hne _ (List.getLast_mem hc))]
    apply (hends _ (List.getLast_mem hc)).2
    exact List.getLast?_eq_some_getLast (hne _ (List.getLast_mem hc))

 
theorem close_clique_chains {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (hQ : G.IsClique Q) (C : List (List V))
    (hne : ∀ c ∈ C, c ≠ []) (hnd : C.flatten.Nodup)
    (hedges : ∀ c ∈ C, c.IsChain G.Adj)
    (hends : ∀ c ∈ C, (∀ x ∈ c.head?, x ∈ Q) ∧ (∀ x ∈ c.getLast?, x ∈ Q))
    (hlen : 3 ≤ C.flatten.length) :
    SimpleGraph.cycleGraph C.flatten.length ⊑ G := by
  have hfn : C.flatten ≠ [] := by intro h; simp [h] at hlen
  have hpchain := clique_chains_flatten hQ C (fun hh => hne [] hh rfl) hnd hedges hends
  let p := SimpleGraph.Walk.ofSupport C.flatten hfn hpchain
  have hp : p.IsPath := p.isPath_def.mpr (by simpa [p] using hnd)
  have hplen : p.length = C.flatten.length - 1 := SimpleGraph.Walk.length_ofSupport _ _
  obtain ⟨hx, hy⟩ := clique_chains_endpoints C hne hends hfn
  have hxy : C.flatten.head hfn ≠ C.flatten.getLast hfn := by
    intro heq
    obtain ⟨v, hv⟩ := (List.Nodup.head_eq_getLast_iff hfn hnd).mp heq
    simp [hv] at hlen
  have hadj := hQ hy hx (Ne.symm hxy)
  have hc : (SimpleGraph.Walk.cons hadj p).IsCycle := by
    apply (p.cons_isCycle_iff hadj).mpr
    refine ⟨hp, ?_⟩
    intro he
    have hh := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
    omega
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, SimpleGraph.Walk.cons hadj p, hc, ?_⟩
  rw [SimpleGraph.Walk.length_cons, hplen]
  omega

theorem PathSystem.flat_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.flatten.length = Q.ncard + P.amount := by
  classical
  have h : Q.ncard ≤ P.chains.flatten.length := by
    have hsub : Q ⊆ (P.chains.flatten.toFinset : Set V) := by
      intro x hx
      exact List.mem_toFinset.mpr (P.cover x hx)
    have hh := Set.ncard_le_ncard hsub
    simpa only [Set.ncard_coe_finset, List.toFinset_card_of_nodup P.nodup] using hh
  dsimp [PathSystem.amount]
  omega

theorem PathSystem.clique_count {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.flatten.countP (fun x => decide (x ∈ Q)) = Q.ncard := by
  classical
  let l := P.chains.flatten.filter (fun x => decide (x ∈ Q))
  have hnd : l.Nodup := P.nodup.filter _
  have he : (l.toFinset : Set V) = Q := by
    ext x
    simp only [Finset.mem_coe, List.mem_toFinset, l, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hx => ⟨P.cover x hx, hx⟩⟩
  have hc := congrArg Set.ncard he
  simpa only [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    l, ← List.countP_eq_length_filter] using hc


theorem PathSystem.chains_length_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.chains.length ≤ Q.ncard := by
  classical
  have hb : ∀ c ∈ P.chains, 1 ≤ c.countP (fun x => decide (x ∈ Q)) := by
    intro c hc
    apply Nat.succ_le_iff.mpr
    apply List.countP_pos_iff.mpr
    let x := c.head (P.nonempty c hc)
    refine ⟨x, List.head_mem _, ?_⟩
    apply decide_eq_true
    exact (P.ends c hc).1 x (List.head?_eq_some_head _)
  have hh := List.sum_le_sum hb
  rw [← List.countP_flatten, P.clique_count] at hh
  simpa using hh

theorem PathSystem.singletons_length_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.singletons.length ≤ Q.ncard :=
  (List.length_filter_le _ _).trans P.chains_length_le

theorem PathSystem.partition {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.usedChains ++ P.singletons).Perm P.chains := by
  classical
  simpa [PathSystem.usedChains, PathSystem.singletons] using
    List.filter_append_perm (fun c : List V => decide (c.length ≠ 1)) P.chains

theorem singletons_flat_length {V : Type*} (C : List (List V))
    (h : ∀ c ∈ C, c.length = 1) : C.flatten.length = C.length := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    rw [List.flatten_cons, List.length_append, h c (by simp),
      ih (fun c hc => h c (by simp [hc])), List.length_cons]
    omega

theorem PathSystem.singleton_flat_length {V : Type*}
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.singletons.flatten.length = P.singletons.length := by
  apply singletons_flat_length
  intro c hc
  exact (List.mem_filter.mp hc).2 |> of_decide_eq_true

theorem PathSystem.closing_interval {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {k : ℕ} (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : Q.ncard ≤ k) (hlo : k + 1 - Q.ncard ≤ P.amount)
    (hhi : P.amount ≤ k + 1 - P.incident) : False := by
  classical
  let u := k + 1 - P.amount - P.incident
  have hi : P.incident ≤ Q.ncard := Nat.sub_le _ _
  have he : P.incident + P.singletons.length = Q.ncard := by
    dsimp [PathSystem.incident]
    have := P.singletons_length_le
    omega
  have hup : u ≤ P.singletons.length := by dsimp [u]; omega
  let C := P.usedChains ++ P.singletons.take u
  have hsub : C.Sublist (P.usedChains ++ P.singletons) :=
    List.Sublist.append (.refl _) (List.take_sublist _ _)
  have hmem : ∀ c ∈ C, c ∈ P.chains := fun c hc => P.partition.subset (hsub.subset hc)
  have hnd : C.flatten.Nodup := hsub.flatten.nodup
    (P.partition.flatten.nodup_iff.mpr P.nodup)
  have hlen₁ := P.partition.flatten.length_eq
  rw [List.flatten_append, List.length_append, P.singleton_flat_length,
    P.flat_length] at hlen₁
  have hlen₂ : (P.singletons.take u).flatten.length = u := by
    rw [singletons_flat_length _ (by
      intro c hc
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take hc)).2),
      List.length_take, Nat.min_eq_left hup]
  have hlen : C.flatten.length = k + 1 := by
    dsimp [C]
    rw [List.flatten_append, List.length_append, hlen₂]
    dsimp [u] at *
    omega
  apply hcycle
  rw [← hlen]
  apply close_clique_chains hQ C (fun c hc => P.nonempty c (hmem c hc)) hnd
    (fun c hc => P.edges c (hmem c hc)) (fun c hc => P.ends c (hmem c hc))
  omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_OptimalSystems
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem PathSystem.exists_optimal {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) {k : ℕ} (ht : Q.ncard ≤ k) :
    ∃ P : PathSystem G Q, P.Optimal k := by
  classical
  let T : ℕ → Prop := fun a => ∃ P : PathSystem G Q, P.amount = a
  let L := Nat.findGreatest T (k - Q.ncard)
  have hT0 : T 0 := ⟨PathSystem.empty G Q, PathSystem.empty_amount G Q⟩
  have hTL : T L := Nat.findGreatest_spec (Nat.zero_le _) hT0
  let E : ℕ → Prop := fun e => ∃ P : PathSystem G Q, P.amount = L ∧ P.edgeCount = e
  have hE : ∃ e, E e := by obtain ⟨P, hP⟩ := hTL; exact ⟨P.edgeCount, P, hP, rfl⟩
  obtain ⟨P, hPL, hPe⟩ := Nat.find_spec hE
  refine ⟨P, ?_, ?_, ?_⟩
  · have hh := Nat.findGreatest_le (P := T) (k - Q.ncard)
    dsimp [L] at hPL
    omega
  · intro R hR
    have hh := Nat.le_findGreatest (P := T) (show R.amount ≤ k - Q.ncard by omega)
      ⟨R, rfl⟩
    dsimp [L] at hPL
    omega
  · intro R hR
    have hh := Nat.find_min' hE (show E R.edgeCount from ⟨R, hR.trans hPL, rfl⟩)
    omega

 

theorem PathSystem.optimality {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    (R : PathSystem G Q)
    (hl : P.amount ≤ R.amount) (htie : P.amount = R.amount → R.edgeCount < P.edgeCount)
    (hu : R.amount ≤ k + 1 - R.incident) : False := by
  by_cases hh : k + 1 - Q.ncard ≤ R.amount
  · exact R.closing_interval hk hQ hcycle ht hh hu
  · have hle := hopt.2.1 R (by omega)
    have heq : R.amount = P.amount := by omega
    have he := hopt.2.2 R heq
    have he' := htie heq.symm
    omega

 
theorem isChain_bridge {V : Type*} {R : V → V → Prop}
    (hR : ∀ ⦃first second⦄, R first second → R second first)
    {x y : V} {u v I : List V} (hu : (x :: u).IsChain R)
    (hv : (y :: v).IsChain R) (hI : (x :: I ++ [y]).IsChain R) :
    ((x :: u).reverse ++ I ++ (y :: v)).IsChain R := by
  have hr : (u.reverse ++ [x]).IsChain R := by
    simpa using List.isChain_reverse.mpr (hu.imp (fun _ _ h => hR h))
  have h₁ : (u.reverse ++ [x] ++ (I ++ [y])).IsChain R :=
    hr.append_overlap hI (by simp)
  have h₂ : ((u.reverse ++ [x] ++ I) ++ [y] ++ v).IsChain R := by
    apply List.IsChain.append_overlap (l₂ := [y]) (by simpa only [List.append_assoc] using h₁)
      (by simpa using hv) (by simp)
  simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h₂

theorem nodup_bridge {V : Type*} {A B C I : List V}
    (h : (A ++ B ++ C).Nodup) (hi : I.Nodup) (hdis : I.Disjoint (A ++ B ++ C)) :
    (A.reverse ++ I ++ B ++ C).Nodup := by
  have hsym := hdis.symm
  simp only [List.nodup_append, List.nodup_reverse, List.mem_append, List.mem_reverse,
    List.disjoint_left] at *
  aesop

 

theorem PathSystem.join_tails {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    (C : List (List V)) {x y : V} (u v I : List V)
    (hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten)
    (hne : ∀ c ∈ C, c ≠ []) (hc : ∀ c ∈ C, c.IsChain G.Adj)
    (hcp : ∀ c ∈ C, c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hce : ∀ c ∈ C, (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q))
    (hu : (x :: u).IsChain G.Adj) (hv : (y :: v).IsChain G.Adj)
    (hup : (x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hvp : (y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hue : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.chains.length = C.length + 1 := by
  classical
  let J := (x :: u).reverse ++ I ++ (y :: v)
  have hJn : J ≠ [] := by simp [J]
  have hnd : (J ++ C.flatten).Nodup := by
    apply nodup_bridge (hperm.nodup_iff.mpr P.nodup) hIn
    apply List.disjoint_left.mpr
    intro a ha hb
    exact List.disjoint_left.mp hId ha (hperm.subset hb)
  have hJe : (∀ a ∈ J.head?, a ∈ Q) ∧ (∀ a ∈ J.getLast?, a ∈ Q) := by
    constructor
    · intro a ha
      apply hue a
      simpa only [J, List.append_assoc, List.head?_append_of_ne_nil _ (by simp : (x :: u).reverse ≠ []),
        List.head?_reverse] using ha
    · intro a ha
      apply hve a
      simpa only [J, ← List.append_assoc,
        List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using ha
  let R : PathSystem G Q :=
    { chains := J :: C
      nonempty := by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
      nodup := hnd
      edges := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
        · exact hc c hc'
      positive := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
        · exact hcp c hc'
      ends := by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
      cover := by
        intro a ha
        have hh := hperm.mem_iff.mpr (P.cover a ha)
        simp only [J, List.flatten_cons, List.mem_append, List.mem_reverse] at hh ⊢
        tauto }
  refine ⟨R, ?_, rfl⟩
  have hh := hperm.length_eq
  rw [P.flat_length] at hh
  change ((x :: u).reverse ++ I ++ (y :: v) ++ C.flatten).length - Q.ncard =
    P.amount + I.length
  simp only [List.length_append, List.length_reverse] at hh ⊢
  omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_MarkedChains
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem markedReps_sublist {V : Type*} (Q : Set V) (b : Bool) (c : List V) :
    (markedReps Q b c).Sublist c := by
  induction c generalizing b with
  | nil => simp [markedReps]
  | cons a c ih =>
    cases b <;> simp only [markedReps, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.singleton_append]
    · exact (ih _).cons _
    · exact (ih _).cons_cons _

theorem markedReps_length {V : Type*} (Q : Set V) (b : Bool) (c : List V)
    (hne : c ≠ []) (hend : ∀ a ∈ c.getLast?, a ∈ Q) :
    (markedReps Q b c).length + 1 = c.countP (· ∈ Q) + (if b then 1 else 0) := by
  induction c generalizing b with
  | nil => contradiction
  | cons a c ih =>
    cases c with
    | nil =>
      have ha : a ∈ Q := hend a (by simp)
      cases b <;> simp [markedReps, ha]
    | cons d c =>
      have he : ∀ v ∈ (d :: c).getLast?, v ∈ Q := by simpa using hend
      have hh := ih (decide (a ∈ Q)) (by simp) he
      cases b <;> by_cases ha : a ∈ Q <;>
        simp [markedReps, ha, List.countP_cons] at hh ⊢ <;> omega



theorem markedCut_cons {V : Type*} {Q : Set V} {b : Bool} {a : V} {A : List V} :
    MarkedCut Q (decide (a ∈ Q)) A ↔ MarkedCut Q b (a :: A) := by
  cases A with
  | nil => simp [MarkedCut]
  | cons d A => simp [MarkedCut]

theorem mem_markedReps {V : Type*} (Q : Set V) (b : Bool) (c : List V) (x : V) :
    x ∈ markedReps Q b c ↔ ∃ A B, c = A ++ x :: B ∧ MarkedCut Q b A := by
  induction c generalizing b with
  | nil => simp [markedReps]
  | cons a c ih =>
    simp only [markedReps, List.mem_append]
    constructor
    · rintro (h | h)
      · have hb : b = true := by cases b <;> simp_all
        have hx : x = a := by simpa [hb] using h
        subst x
        exact ⟨[], c, rfl, Or.inl ⟨rfl, hb⟩⟩
      · obtain ⟨A, B, h, hcut⟩ := (ih _).mp h
        exact ⟨a :: A, B, by simp [h], markedCut_cons.mp hcut⟩
    · rintro ⟨A, B, h, hcut⟩
      cases A with
      | nil =>
        have he : a = x ∧ c = B := by simpa using h
        have hb : b = true := by simpa [MarkedCut] using hcut
        simp [hb, he.1]
      | cons d A =>
        have he : a = d ∧ c = A ++ x :: B := by simpa using h
        rcases he with ⟨rfl, he⟩
        right
        exact (ih _).mpr ⟨A, B, he, markedCut_cons.mpr hcut⟩

theorem markedReps_flatten_sublist {V : Type*} (Q : Set V) (C : List (List V)) :
    (C.map (markedReps Q true)).flatten.Sublist C.flatten := by
  induction C with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (markedReps_sublist Q true c).append ih

theorem PathSystem.reps_sublist {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.reps.Sublist P.chains.flatten :=
  markedReps_flatten_sublist Q P.chains

theorem markedReps_flatten_length {V : Type*} (Q : Set V) (C : List (List V))
    (hc : ∀ c ∈ C, c ≠ [] ∧ ∀ a ∈ c.getLast?, a ∈ Q) :
    (C.map (markedReps Q true)).flatten.length = C.flatten.countP (· ∈ Q) := by
  induction C with
  | nil => simp
  | cons c cs ih =>
    have he := markedReps_length Q true c (hc c (by simp)).1 (hc c (by simp)).2
    have ht := ih (fun l hl => hc l (by simp [hl]))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.countP_append]
    simp only [↓reduceIte] at he
    omega

theorem PathSystem.reps_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) : P.reps.length = Q.ncard :=
  (markedReps_flatten_length Q P.chains
    (fun c hc => ⟨P.nonempty c hc, (P.ends c hc).2⟩)).trans P.clique_count

theorem markedCut_of_split {V : Type*} {Q : Set V} {b : Bool} {c A B : List V} {x : V}
    (hn : c.Nodup) (hx : x ∈ markedReps Q b c) (hc : c = A ++ x :: B) :
    MarkedCut Q b A := by
  obtain ⟨A', B', hc', hcut⟩ := (mem_markedReps Q b c x).mp hx
  have hh := List.nodup_append.mp (hc ▸ hn)
  have hnA : x ∉ A := fun h => hh.2.2 x h x (by simp) rfl
  have hnB : x ∉ B := (List.nodup_cons.mp hh.2.1).1
  have he := (List.append_cons_inj_of_notMem hnA hnB).mp (hc.symm.trans hc')
  simpa only [he.1] using hcut

theorem two_mem_ordered {V : Type*} {c : List V} {x y : V}
    (hx : x ∈ c) (hy : y ∈ c) (hne : x ≠ y) :
    (∃ A u v, c = A ++ (x :: u) ++ y :: v) ∨
    (∃ A u v, c = A ++ (y :: u) ++ x :: v) := by
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hx
  have hy' : y ∈ A ∨ y ∈ B := by simpa [hne.symm] using hy
  rcases hy' with h | h
  · obtain ⟨C, D, rfl⟩ := List.mem_iff_append.mp h
    exact Or.inr ⟨C, D, B, by simp only [List.append_assoc, List.cons_append]⟩
  · obtain ⟨C, D, rfl⟩ := List.mem_iff_append.mp h
    exact Or.inl ⟨A, C, D, by simp only [List.append_assoc, List.cons_append]⟩

theorem markedCuts_ordered {V : Type*} {Q : Set V} {b : Bool} {c : List V}
    {x y : V} (hn : c.Nodup) (hx : x ∈ markedReps Q b c)
    (hy : y ∈ markedReps Q b c) (A u v : List V)
    (hc : c = A ++ (x :: u) ++ y :: v) :
    MarkedCut Q b A ∧ ∀ a ∈ (x :: u).getLast?, a ∈ Q := by
  refine ⟨markedCut_of_split hn hx (by simpa only [List.append_assoc, List.cons_append] using hc), ?_⟩
  have hh := markedCut_of_split hn hy hc
  rcases hh with ⟨hh, _⟩ | ⟨_, hh⟩
  · simp at hh
  · simpa only [List.getLast?_append_of_ne_nil _ (by simp : x :: u ≠ [])] using hh

theorem mem_prefixChains {V : Type*} {A c : List V} :
    c ∈ prefixChains A ↔ c = A ∧ A ≠ [] := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem prefix_ends {V : Type*} {Q : Set V} {b : Bool} {c A B : List V}
    (hh : ∀ a ∈ c.head?, a ∈ Q) (hc : c = A ++ B) (hcut : MarkedCut Q b A)
    (hA : A ≠ []) :
    (∀ a ∈ A.head?, a ∈ Q) ∧ (∀ a ∈ A.getLast?, a ∈ Q) := by
  constructor
  · simpa only [hc, List.head?_append_of_ne_nil _ hA] using hh
  · rcases hcut with ⟨h, _⟩ | ⟨_, h⟩
    · contradiction
    · exact h

theorem PathSystem.closed_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) : ClosedChain G Q c :=
  ⟨P.nonempty c hc, P.edges c hc, P.positive c hc, P.ends c hc⟩

theorem ClosedChain.cut {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c A : List V} {x : V} {u : List V} (hc : ClosedChain G Q c)
    (he : c = A ++ x :: u) (hcut : MarkedCut Q true A) :
    (∀ d ∈ prefixChains A, ClosedChain G Q d) ∧ LooseTail G Q (x :: u) := by
  have hed : (A ++ x :: u).IsChain G.Adj := he ▸ hc.edges
  have hpo : (A ++ x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := he ▸ hc.positive
  constructor
  · intro d hd
    obtain ⟨rfl, hA⟩ := mem_prefixChains.mp hd
    exact ⟨hA, hed.left_of_append, hpo.left_of_append, prefix_ends hc.ends.1 he hcut hA⟩
  · refine ⟨hed.right_of_append, hpo.right_of_append, ?_⟩
    simpa only [he, List.getLast?_append_of_ne_nil _ (by simp : x :: u ≠ [])] using hc.ends.2

theorem perm_reorder_four {V : Type*} (A U B W D : List V) :
    (U ++ W ++ (A ++ B ++ D)).Perm ((A ++ U) ++ (B ++ W) ++ D) := by
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

theorem PathSystem.join_distinct_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: d :: D))
  have hdd := P.closed_chain (hP.mem_iff.mpr (by simp : d ∈ c :: d :: D))
  obtain ⟨hA, hu⟩ := hcc.cut hc hcutc
  obtain ⟨hB, hv⟩ := hdd.cut hd hcutd
  let C := prefixChains A ++ prefixChains B ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hA l hl
    · exact hB l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc, hd]
    simpa only [List.append_assoc] using perm_reorder_four A (x :: u) B (y :: v) D.flatten
  obtain ⟨R, hR, _⟩ := P.join_tails C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
  exact ⟨R, hR⟩

theorem PathSystem.join_same_chain {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: D))
  obtain ⟨hA, hu⟩ := hcc.cut (by simpa only [List.append_assoc, List.cons_append] using hc) hcut
  have he : ((x :: u) ++ y :: v).IsChain G.Adj := by simpa only [List.cons_append] using hu.edges
  have hp : ((x :: u) ++ y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
    simpa only [List.cons_append] using hu.positive
  have hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q := by
    simpa only [hc, List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using hcc.ends.2
  let C := prefixChains A ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hA l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  obtain ⟨R, hR, _⟩ := P.join_tails C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
    hum hve hI hIp hIn hId
  exact ⟨R, hR⟩

theorem PathSystem.representative_replacement {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) {x y : V}
    (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxy : x ≠ y) (I : List V)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length := by
  classical
  obtain ⟨rc, hrc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
  obtain ⟨rd, hrd, hyd⟩ := List.mem_flatten.mp hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrd
  have hnc := (List.nodup_flatten.mp P.nodup).1 c hc
  by_cases hcd : c = d
  · subst d
    have hp := List.perm_cons_erase hc
    rcases two_mem_ordered ((markedReps_sublist Q true c).subset hxc)
      ((markedReps_sublist Q true c).subset hyd) hxy with hh | hh
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hxc hyd A u v he
      exact P.join_same_chain (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hyd hxc A u v he
      have hi : (y :: I.reverse ++ [x]).IsChain G.Adj := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hI.imp (fun _ _ h => h.symm))
      have hip : (y :: I.reverse ++ [x]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hIp.imp (fun _ _ h => h.symm))
      obtain ⟨R, hR⟩ := P.join_same_chain (P.chains.erase c) hp A u v I.reverse he hA hu hi hip
        (List.nodup_reverse.mpr hIn) (by simpa using hId)
      exact ⟨R, by simpa using hR⟩
  · have hp₁ := List.perm_cons_erase hc
    have hd' : d ∈ P.chains.erase c := (List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
    have hp₂ := List.perm_cons_erase hd'
    have hp := hp₁.trans (hp₂.cons c)
    obtain ⟨A, u, hec, hcutc⟩ := (mem_markedReps Q true c x).mp hxc
    obtain ⟨B, v, hed, hcutd⟩ := (mem_markedReps Q true d y).mp hyd
    exact P.join_distinct_chains ((P.chains.erase c).erase d) hp
      A u B v I hec hed hcutc hcutd hI hIp hIn hId

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ChainProfiles
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem first_mem_split {V : Type*} (Q : Set V) (c : List V)
    (h : ∃ x ∈ c, x ∈ Q) :
    ∃ I x B, c = I ++ x :: B ∧ (∀ z ∈ I, z ∉ Q) ∧ x ∈ Q := by
  classical
  induction c with
  | nil => simp at h
  | cons x c ih =>
    by_cases hx : x ∈ Q
    · exact ⟨[], x, c, rfl, by simp, hx⟩
    · have ht : ∃ y ∈ c, y ∈ Q := by
        obtain ⟨y, hy, hyQ⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hx hyQ).elim
        · exact ⟨y, hy, hyQ⟩
      obtain ⟨I, y, B, he, hout, hy⟩ := ih ht
      refine ⟨x :: I, y, B, ?_, ?_, hy⟩
      · simp only [he, List.cons_append]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hout z hz

theorem ChainAmounts.exists {V : Type*} {Q : Set V} {G : SimpleGraph V}
    (c : List V) (hc : ClosedChain G Q c) : ∃ A, ChainAmounts Q c A := by
  cases c with
  | nil => exact (hc.nonempty rfl).elim
  | cons x l =>
    have hx : x ∈ Q := hc.ends.1 x (by simp)
    by_cases hl : l = []
    · subst l
      exact ⟨[], .singleton x hx⟩
    · have hh : ∃ y ∈ l, y ∈ Q := by
        refine ⟨l.getLast hl, List.getLast_mem hl, ?_⟩
        apply hc.ends.2
        simpa only [List.getLast?_cons_of_ne_nil hl, List.getLast?_eq_some_getLast hl] using
          (Option.mem_def.mpr rfl : l.getLast hl ∈ some (l.getLast hl))
      obtain ⟨I, y, B, he, hout, hy⟩ := first_mem_split Q l hh
      have hec : x :: l = (x :: I) ++ y :: B := by simp [he]
      have hI : I ≠ [] := by
        intro hi
        subst I
        have hp := hc.positive
        rw [he] at hp
        exact hp.rel.elim (fun h => h hx) (fun h => h hy)
      have ht : ClosedChain G Q (y :: B) := {
        nonempty := by simp
        edges := by rw [hec] at hc; exact hc.edges.right_of_append
        positive := by rw [hec] at hc; exact hc.positive.right_of_append
        ends := ⟨by simpa using hy, by
          simpa only [hec, List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using hc.ends.2⟩ }
      obtain ⟨A, hA⟩ := ChainAmounts.exists (y :: B) ht
      exact ⟨I.length :: A, by simpa only [he] using ChainAmounts.step x y I B A hx hI hout hA⟩
termination_by c.length

 theorem ChainAmounts.head_mem {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) : ∀ x ∈ c.head?, x ∈ Q := by
  cases h <;> simp_all

theorem ChainAmounts.deletion_split {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) {a : ℕ} (ha : a ∈ A) :
    ∃ U x I y B AL AR, c = U ++ x :: (I ++ y :: B) ∧ I.length = a ∧
      (∀ z ∈ I, z ∉ Q) ∧ ChainAmounts Q (U ++ [x]) AL ∧
      ChainAmounts Q (y :: B) AR ∧ A = AL ++ a :: AR := by
  induction h with
  | singleton x hx => simp at ha
  | step p q J C A hp hJ hJout htail ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[], p, J, q, C, [], A, rfl, rfl, hJout, .singleton p hp, htail, rfl⟩
    · obtain ⟨U, x, I, y, B, AL, AR, he, hi, hout, hleft, hright, hA⟩ := ih ha
      have hne : U ++ [x] ≠ [] := by simp
      obtain ⟨q', D, hD⟩ := List.exists_cons_of_ne_nil hne
      have hq : q' = q := by
        have hh := congrArg List.head? he
        have hh' := congrArg List.head? hD
        cases U <;> simp_all
      subst q'
      have hleft' : ChainAmounts Q ((p :: (J ++ U)) ++ [x]) (J.length :: AL) := by
        have hc := ChainAmounts.step p q J D AL hp hJ hJout (hD ▸ hleft)
        simpa only [← hD, List.append_assoc, List.cons_append] using hc
      refine ⟨p :: (J ++ U), x, I, y, B, J.length :: AL, AR, ?_, hi, hout,
        hleft', hright, ?_⟩
      · rw [he]
        simp only [List.append_assoc, List.cons_append]
      · simp only [hA, List.cons_append]


theorem PathSystem.exists_profile {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : ∃ A, AmountProfile P A := by
  have hh : ∀ c ∈ P.chains, ∃ A, ChainAmounts Q c A :=
    fun c hc => ChainAmounts.exists c (P.closed_chain hc)
  have hex : ∃ D, List.Forall₂ (ChainAmounts Q) P.chains D := by
    generalize P.chains = C at hh ⊢
    revert hh
    induction C with
    | nil => intro _; exact ⟨[], .nil⟩
    | cons c C ih =>
      intro hh
      obtain ⟨A, hA⟩ := hh c (by simp)
      obtain ⟨D, hD⟩ := ih (fun d hd => hh d (by simp [hd]))
      exact ⟨A :: D, .cons hA hD⟩
  obtain ⟨D, hD⟩ := hex
  exact ⟨D.flatten, ⟨D, hD, List.Perm.refl _⟩⟩

theorem AmountProfile.count {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) :
    A.sum = P.amount ∧ A.length = P.edgeCount ∧ ∀ a ∈ A, 1 ≤ a := by
  obtain ⟨D, hD, hperm⟩ := h
  have hh : P.chains.flatten.countP (fun x => decide (x ∈ Q)) = D.flatten.length + P.chains.length ∧
      P.chains.flatten.length = D.flatten.sum + D.flatten.length + P.chains.length ∧
      ∀ a ∈ D.flatten, 1 ≤ a := by
    clear hperm
    generalize P.chains = C at hD ⊢
    induction hD with
    | nil => simp
    | @cons c B C D hc hC ih =>
      obtain ⟨hq, hl, hp⟩ := hc.count
      rcases ih with ⟨hq', hl', hp'⟩
      constructor
      · simp only [List.flatten_cons, List.countP_append, List.length_append, List.length_cons]
        omega
      constructor
      · simp only [List.flatten_cons, List.length_append, List.sum_append, List.length_cons]
        omega
      · intro a ha
        simp only [List.flatten_cons, List.mem_append] at ha
        exact ha.elim (hp a) (hp' a)
  rw [P.clique_count, P.flat_length, hperm.length_eq, hperm.sum_eq] at hh
  dsimp [PathSystem.edgeCount]
  exact ⟨by omega, by omega, fun a ha => hh.2.2 a (hperm.mem_iff.mpr ha)⟩

theorem AmountProfile.perm {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A B : List ℕ} (h : AmountProfile P A) (hp : A.Perm B) :
    AmountProfile P B := by
  obtain ⟨D, hD, hDA⟩ := h
  exact ⟨D, hD, hDA.trans hp⟩

theorem ChainAmounts.ends {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) :
    (∀ x ∈ c.head?, x ∈ Q) ∧ ∀ y ∈ c.getLast?, y ∈ Q := by
  induction h with
  | singleton x hx => simpa using And.intro hx hx
  | step x y I B A hx hI hout htail ih =>
    constructor
    · simpa using hx
    · simpa only [show x :: (I ++ y :: B) = (x :: I) ++ y :: B from by simp,
        List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using ih.2

theorem forall₂_select_right {α β : Type*} {R : α → β → Prop}
    {C : List α} {D : List β} (h : List.Forall₂ R C D) {b : β} (hb : b ∈ D) :
    ∃ C₁ c C₂ D₁ D₂, C = C₁ ++ c :: C₂ ∧ D = D₁ ++ b :: D₂ ∧
      List.Forall₂ R C₁ D₁ ∧ R c b ∧ List.Forall₂ R C₂ D₂ := by
  induction h with
  | nil => simp at hb
  | @cons c d C D hcd hCD ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨[], c, C, [], D, rfl, rfl, .nil, hcd, hCD⟩
    · obtain ⟨C₁, c', C₂, D₁, D₂, hC, hD, hpre, hcc, hpost⟩ := ih hb
      exact ⟨c :: C₁, c', C₂, d :: D₁, D₂,
        by simp [hC], by simp [hD], .cons hcd hpre, hcc, hpost⟩

theorem AmountProfile.delete {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) {a : ℕ} (ha : a ∈ A) :
    ∃ R : PathSystem G Q, ∃ B : List ℕ, AmountProfile R B ∧ (a :: B).Perm A := by
  obtain ⟨D, hD, hDA⟩ := h
  obtain ⟨C, hCD, haC⟩ := List.mem_flatten.mp (hDA.mem_iff.mpr ha)
  obtain ⟨CP, c, CS, DP, DS, hP, hD', hpre, hcC, hpost⟩ := forall₂_select_right hD hCD
  obtain ⟨U, x, I, y, B, AL, AR, he, hIa, hIo, hleft, hright, hC⟩ := hcC.deletion_split haC
  let J := U ++ [x]
  let K := y :: B
  let newC := CP ++ J :: K :: CS
  let newD := DP ++ AL :: AR :: DS
  have hec : c = J ++ I ++ K := by simpa only [J, K, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using he
  have hperm : (I ++ newC.flatten).Perm P.chains.flatten := by
    rw [hP]
    dsimp [newC]
    simp only [List.flatten_append, List.flatten_cons, hec]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hnd := List.nodup_append.mp (hperm.nodup_iff.mpr P.nodup)
  have hcc := P.closed_chain (by rw [hP]; simp : c ∈ P.chains)
  have hj : ClosedChain G Q J := {
    nonempty := by simp [J]
    edges := by rw [hec] at hcc; exact hcc.edges.left_of_append.left_of_append
    positive := by rw [hec] at hcc; exact hcc.positive.left_of_append.left_of_append
    ends := hleft.ends }
  have hk : ClosedChain G Q K := {
    nonempty := by simp [K]
    edges := by rw [hec] at hcc; exact hcc.edges.right_of_append
    positive := by rw [hec] at hcc; exact hcc.positive.right_of_append
    ends := hright.ends }
  have holds : ∀ l ∈ newC, ClosedChain G Q l := by
    intro l hl
    simp only [newC, List.mem_append, List.mem_cons] at hl
    rcases hl with hl | rfl | rfl | hl
    · exact P.closed_chain (by rw [hP]; simp [hl])
    · exact hj
    · exact hk
    · exact P.closed_chain (by rw [hP]; simp [hl])
  let R : PathSystem G Q := {
    chains := newC
    nonempty := fun l hl => (holds l hl).nonempty
    nodup := hnd.2.1
    edges := fun l hl => (holds l hl).edges
    positive := fun l hl => (holds l hl).positive
    ends := fun l hl => (holds l hl).ends
    cover := by
      intro v hv
      have hv' := hperm.mem_iff.mpr (P.cover v hv)
      rcases List.mem_append.mp hv' with hvi | hvn
      · exact (hIo v hvi hv).elim
      · exact hvn }
  have hd : List.Forall₂ (ChainAmounts Q) R.chains newD :=
    List.rel_append hpre (.cons hleft (.cons hright hpost))
  refine ⟨R, newD.flatten, ⟨newD, hd, List.Perm.refl _⟩, ?_⟩
  apply List.Perm.trans _ hDA
  rw [hD', hC]
  dsimp [newD]
  simp only [List.flatten_append, List.flatten_cons]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
  ac_rfl

theorem AmountProfile.erase {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A) {a : ℕ} (ha : a ∈ A) :
    ∃ R : PathSystem G Q, AmountProfile R (A.erase a) := by
  obtain ⟨R, B, hB, hp⟩ := h.delete ha
  have he : (a :: B).Perm (a :: A.erase a) := hp.trans (List.perm_cons_erase ha)
  exact ⟨R, hB.perm (List.Perm.cons_inv he)⟩

theorem AmountProfile.drop_prefix {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (C B : List ℕ) {P : PathSystem G Q} (h : AmountProfile P (C ++ B)) :
    ∃ R : PathSystem G Q, AmountProfile R B := by
  induction C generalizing P with
  | nil => exact ⟨P, h⟩
  | cons a C ih =>
    obtain ⟨R, hR⟩ := h.erase (by simp : a ∈ (a :: C) ++ B)
    have hr : AmountProfile R (C ++ B) := by simpa using hR
    exact ih hr

theorem AmountProfile.prune {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A B : List ℕ} (h : AmountProfile P A) (hB : B.Sublist A) :
    ∃ R : PathSystem G Q, AmountProfile R B := by
  obtain ⟨C, hAC⟩ := hB.exists_perm_append
  exact (h.perm (hAC.trans (List.perm_append_comm))).drop_prefix C B

theorem PathSystem.incident_le_twice_edgeCount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident ≤ 2 * P.edgeCount := by
  classical
  have hb : ∀ c ∈ P.chains,
      2 ≤ c.countP (fun v => decide (v ∈ Q)) + if c.length = 1 then 1 else 0 := by
    intro c hc
    obtain ⟨A, hA⟩ := ChainAmounts.exists c (P.closed_chain hc)
    have hh := hA.count
    by_cases he : c.length = 1
    · simp only [he, ite_true, if_true]
      omega
    · simp only [he, ite_false, if_false]
      have hn : A.length ≠ 0 := by
        intro hn
        have heA : A = [] := List.length_eq_zero_iff.mp hn
        simp only [heA, List.sum_nil, List.length_nil] at hh
        omega
      omega
  have hs := List.sum_le_sum hb
  have he : (P.chains.map (fun c =>
      c.countP (fun v => decide (v ∈ Q)) + if c.length = 1 then 1 else 0)).sum =
      Q.ncard + P.singletons.length := by
    rw [List.sum_map_add, ← List.countP_flatten, P.clique_count]
    congr 1
    simp only [PathSystem.singletons, ← List.countP_eq_length_filter]
    induction P.chains with
    | nil => simp
    | cons c C ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, decide_eq_true_eq]
      omega
  rw [he] at hs
  have hh := P.chains_length_le
  have hss := P.singletons_length_le
  have hleft : (P.chains.map (fun _ => 2)).sum = 2 * P.chains.length := by simp [Nat.mul_comm]
  rw [hleft] at hs
  dsimp [PathSystem.incident, PathSystem.edgeCount]
  omega

theorem ChainAmounts.run_bound {V : Type*} {Q : Set V} {c I : List V} {A : List ℕ}
    (h : ChainAmounts Q c A) (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
    (hin : I <:+: c) : ∃ a ∈ A, I.length ≤ a := by
  induction h with
  | singleton x hx =>
    obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil I hI
    have he : z = x := by simpa using hin.sublist.subset hz
    subst z
    exact (hout x hz hx).elim
  | step x y J B A hx hJ hJo htail ih =>
    have hy : y ∈ Q := htail.head_mem y (by simp)
    have hin' : I <:+: (x :: J) ++ y :: B := by simpa only [List.cons_append] using hin
    rcases List.infix_append_iff_ne_nil.mp hin' with hleft | hright | ⟨I₁, I₂, hn₁, hn₂, he, hs, hp⟩
    · have hh : I.Sublist J := by
        rcases List.sublist_cons_iff.mp hleft.sublist with h | ⟨D, hd, _⟩
        · exact h
        · exact (hout x (by simp [hd]) hx).elim
      exact ⟨J.length, by simp, hh.length_le⟩
    · obtain ⟨a, ha, hIa⟩ := ih hright
      exact ⟨a, by simp [ha], hIa⟩
    · obtain ⟨z, Z, hz⟩ := List.exists_cons_of_ne_nil hn₂
      obtain ⟨T, hT⟩ := hp
      rw [hz] at hT
      have hzy : z = y := (List.cons.inj hT).1
      subst z
      have hyI : y ∈ I := by rw [he, hz]; simp
      exact (hout y hyI hy).elim

theorem AmountProfile.run_bound {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {P : PathSystem G Q} {A : List ℕ} (h : AmountProfile P A)
    {c I : List V} (hc : c ∈ P.chains) (hI : I ≠ []) (hout : ∀ z ∈ I, z ∉ Q)
    (hin : I <:+: c) : ∃ a ∈ A, I.length ≤ a := by
  obtain ⟨D, hD, hDA⟩ := h
  obtain ⟨DP, B, DS, CP, CS, hDs, _, _, hBc, _⟩ := forall₂_select_right hD.flip hc
  obtain ⟨a, ha, hIa⟩ := ChainAmounts.run_bound hBc hI hout hin
  refine ⟨a, hDA.mem_iff.mp ?_, hIa⟩
  exact List.mem_flatten.mpr ⟨B, by rw [hDs]; simp, ha⟩

theorem list_minimal_above (A : List ℕ) (h : ℕ) (hh : h ≤ A.sum) :
    ∃ B : List ℕ, B.Sublist A ∧ h ≤ B.sum ∧ ∀ a ∈ B, (B.erase a).sum < h := by
  let E : ℕ → Prop := fun n => ∃ B : List ℕ, B.Sublist A ∧ h ≤ B.sum ∧ B.length = n
  have hex : ∃ n, E n := ⟨A.length, A, .refl _, hh, rfl⟩
  obtain ⟨B, hB, hb, hn⟩ := Nat.find_spec hex
  refine ⟨B, hB, hb, ?_⟩
  intro a ha
  by_contra! he
  have hm := Nat.find_min' hex (show E (B.erase a).length from
    ⟨B.erase a, (List.erase_sublist).trans hB, he, rfl⟩)
  have hl := List.length_erase_add_one ha
  omega

theorem list_sum_erase {A : List ℕ} {a : ℕ} (ha : a ∈ A) :
    A.sum = a + (A.erase a).sum := by
  simpa using (List.perm_cons_erase ha).sum_eq

theorem list_sum_lower (A : List ℕ) (b : ℕ) (h : ∀ a ∈ A, b ≤ a) :
    b * A.length ≤ A.sum := by
  have hh := List.sum_le_sum h
  simpa [Nat.mul_comm] using hh

theorem increment_numeric {t L r j s : ℕ} (ht : 9 ≤ t) (hL : L ≤ t + 1)
    (hwr : t + 1 ≤ 2 * r + j) (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (hs : s + 1 = r) (hb : (j + 2) * s ≤ L) : False := by
  interval_cases j <;> nlinarith

 

theorem PathSystem.small_increment {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k d : ℕ} (P R : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hR : R.amount = P.amount + d)
    (he : R.edgeCount ≤ P.edgeCount + 1) {A : List ℕ}
    (hA : AmountProfile R A) {b : ℕ} (hb : b ∈ A) (hbd : d ≤ b) :
    P.amount = k - Q.ncard ∧ R.edgeCount = P.edgeCount + 1 ∧
      2 ≤ d ∧ ∀ a ∈ A, d ≤ a := by
  let h := k + 1 - Q.ncard
  have hL : P.amount < h := hopt.1
  have hh : h ≤ R.amount := by
    by_contra! hh
    have hx := hopt.2.1 R hh
    omega
  obtain ⟨hsum, hlen, hpos⟩ := hA.count
  obtain ⟨B, hBA, hBh, hBmin⟩ := list_minimal_above A h (by omega)
  obtain ⟨T, hT⟩ := hA.prune hBA
  obtain ⟨hTS, hTL, hTP⟩ := hT.count
  have hsumB : B.sum ≤ A.sum := hBA.sum_le_sum (fun _ _ => Nat.zero_le _)
  have hlengthB : B.length ≤ A.length := hBA.length_le
  have hEr : (A.erase b).sum ≤ P.amount := by
    have hs := list_sum_erase hb
    omega
  have hbB : b ∈ B := by
    by_contra hbB
    have hs := (hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)
    rw [List.erase_of_not_mem hbB] at hs
    omega
  have hsumEr : (B.erase b).sum ≤ P.amount :=
    le_trans ((hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)) hEr
  let j := B.sum - h
  have hj : B.sum = h + j := by dsimp [j]; omega
  have hj5 : j ≤ 5 := by omega
  have hwi := T.incident_le_twice_edgeCount
  have hwt : T.incident ≤ Q.ncard := Nat.sub_le _ _
  have hw : k + 1 - T.incident < T.amount := by
    by_contra! hw
    exact T.closing_interval (by omega) hQ hcycle htk (by omega) hw
  have hj1 : 1 ≤ j := by dsimp [h] at hj; omega
  have hwr : Q.ncard + 1 ≤ 2 * B.length + j := by dsimp [h] at hj; omega
  have hsmall : ∃ a ∈ B, a = j + 1 := by
    by_contra! hn
    have hge : ∀ a ∈ B, j + 2 ≤ a := by
      intro a ha
      have hm := hBmin a ha
      have hs := list_sum_erase ha
      have hne := hn a ha
      omega
    have hbg := list_sum_lower (B.erase b) (j + 2)
      (fun a ha => hge a (List.mem_of_mem_erase ha))
    have hbl := List.length_erase_add_one hbB
    have hLt : P.amount ≤ Q.ncard + 1 := by dsimp [h] at hL; omega
    exact increment_numeric ht hLt hwr hj1 hj5 hbl (le_trans hbg hsumEr)
  obtain ⟨a, ha, har⟩ := hsmall
  obtain ⟨U, hU⟩ := hT.erase ha
  have hcU := hU.count
  have hSU := list_sum_erase ha
  have hLU := List.length_erase_add_one ha
  have hUamount : U.amount = h - 1 := by omega
  have hUL : U.amount ≤ P.amount := hopt.2.1 U (by dsimp [h] at *; omega)
  have hLeq : P.amount = k - Q.ncard := by dsimp [h] at *; omega
  have hULeq : U.amount = P.amount := by dsimp [h] at *; omega
  have hUE := hopt.2.2 U hULeq
  have heq : R.edgeCount = P.edgeCount + 1 := by omega
  have hBEq : B = A := hBA.eq_of_length (by omega)
  subst B
  have hjd : j + 1 = d := by dsimp [h] at hj; omega
  refine ⟨hLeq, heq, by omega, ?_⟩
  intro a ha
  have hm := hBmin a ha
  have hs := list_sum_erase ha
  omega

theorem PathSystem.join_tails_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    (C : List (List V)) {x y : V} (u v I : List V)
    (hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten)
    (hne : ∀ c ∈ C, c ≠ []) (hc : ∀ c ∈ C, c.IsChain G.Adj)
    (hcp : ∀ c ∈ C, c.IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hce : ∀ c ∈ C, (∀ a ∈ c.head?, a ∈ Q) ∧ (∀ a ∈ c.getLast?, a ∈ Q))
    (hu : (x :: u).IsChain G.Adj) (hv : (y :: v).IsChain G.Adj)
    (hup : (x :: u).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hvp : (y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hue : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: C := by
  classical
  let J := (x :: u).reverse ++ I ++ (y :: v)
  have hJn : J ≠ [] := by simp [J]
  have hnd : (J ++ C.flatten).Nodup := by
    apply nodup_bridge (hperm.nodup_iff.mpr P.nodup) hIn
    apply List.disjoint_left.mpr
    intro a ha hb
    exact List.disjoint_left.mp hId ha (hperm.subset hb)
  have hJe : (∀ a ∈ J.head?, a ∈ Q) ∧ (∀ a ∈ J.getLast?, a ∈ Q) := by
    constructor
    · intro a ha
      apply hue a
      simpa only [J, List.append_assoc, List.head?_append_of_ne_nil _ (by simp : (x :: u).reverse ≠ []),
        List.head?_reverse] using ha
    · intro a ha
      apply hve a
      simpa only [J, ← List.append_assoc,
        List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using ha
  let R : PathSystem G Q :=
    { chains := J :: C
      nonempty := by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
      nodup := hnd
      edges := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
        · exact hc c hc'
      positive := by
        intro c hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
        · exact hcp c hc'
      ends := by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
      cover := by
        intro a ha
        have hh := hperm.mem_iff.mpr (P.cover a ha)
        simp only [J, List.flatten_cons, List.mem_append, List.mem_reverse] at hh ⊢
        tauto }
  refine ⟨R, ?_, rfl⟩
  have hh := hperm.length_eq
  rw [P.flat_length] at hh
  change ((x :: u).reverse ++ I ++ (y :: v) ++ C.flatten).length - Q.ncard =
    P.amount + I.length
  simp only [List.length_append, List.length_reverse] at hh ⊢
  omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_SystemInsertion
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem PathSystem.vertices_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.vertices.ncard = Q.ncard + P.amount := by
  classical
  have he : P.vertices = (↑P.chains.flatten.toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup P.nodup, P.flat_length]

theorem OutsidePath.to_list {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) :
    ∃ I : List V, I.length = d ∧ (x :: I ++ [y]).IsChain G.Adj ∧
      I.Nodup ∧ ∀ a ∈ I, a ∉ X := by
  obtain ⟨hx, hy, hxy, p, hp, hlen, hs⟩ := h
  cases p with
  | nil => simp at hlen
  | cons hadj q =>
    let I := q.support.dropLast
    have he : q.support = I ++ [y] := by
      simpa only [I, q.getLast_support] using (List.dropLast_concat_getLast q.support_ne_nil).symm
    have hn : (x :: I ++ [y]).Nodup := by
      simpa only [SimpleGraph.Walk.support_cons, he, List.cons_append] using hp.support_nodup
    have htail := (List.nodup_cons.mp hn).2
    have hi := (List.nodup_append.mp htail).1
    have hxI : x ∉ I := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
    have hyI : y ∉ I := fun hy => (List.nodup_append.mp htail).2.2 y hy y (by simp) rfl
    refine ⟨I, ?_, ?_, hi, ?_⟩
    · have hl := q.length_support
      rw [he, List.length_append, List.length_singleton] at hl
      simp only [SimpleGraph.Walk.length_cons] at hlen
      omega
    · simpa only [SimpleGraph.Walk.support_cons, he, List.cons_append] using
        (SimpleGraph.Walk.cons hadj q).isChain_adj_support
    · intro a ha haX
      rcases hs a (by simp only [SimpleGraph.Walk.support_cons, he, List.mem_cons,
        List.mem_append]; exact Or.inr (Or.inl ha)) haX with rfl | rfl
      · exact hxI ha
      · exact hyI ha

theorem positive_interior_chain {V : Type*} {Q : Set V} {x y : V} {I : List V}
    (hne : I ≠ []) (hout : ∀ a ∈ I, a ∉ Q) :
    (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
  induction I generalizing x with
  | nil => contradiction
  | cons a I ih =>
    have ha := hout a (by simp)
    apply List.isChain_cons.mpr
    constructor
    · intro b hb
      have he : a = b := by simpa using hb
      exact Or.inr (he ▸ ha)
    · cases I with
      | nil => simpa using (Or.inl ha : a ∉ Q ∨ y ∉ Q)
      | cons b I =>
        exact ih (by simp) (fun c hc => hout c (by simp [hc]))

theorem PathSystem.no_one_representatives {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) :
    ¬ OutsidePath G P.vertices x y 1 := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hIo⟩ := hp.to_list
  have hip : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) :=
    positive_interior_chain (by intro h; simp [h] at hIl)
      (fun a ha hQ => hIo a ha (P.cover a hQ))
  have hid : I.Disjoint P.chains.flatten := List.disjoint_left.mpr hIo
  obtain ⟨R, hR⟩ := P.representative_replacement hx hy hp.2.2.1 I hI hip hIn hid
  have hr : R.incident ≤ Q.ncard := Nat.sub_le _ _
  have hh := hopt.1
  apply P.optimality hopt hk hQ hcycle ht R (by omega) (by omega)
  omega

theorem isChain_insert_step {V : Type*} {R : V → V → Prop} {A I B : List V} {x y : V}
    (hc : (A ++ x :: y :: B).IsChain R) (hI : (x :: I ++ [y]).IsChain R) :
    (A ++ x :: I ++ y :: B).IsChain R := by
  have hp : (A ++ [x]).IsChain R := by
    apply List.IsChain.left_of_append (l₂ := y :: B)
    simpa only [List.append_assoc, List.singleton_append] using hc
  have hs : (y :: B).IsChain R := by
    apply List.IsChain.right_of_append (l₁ := A ++ [x])
    simpa only [List.append_assoc, List.singleton_append] using hc
  have h₁ : (A ++ [x] ++ (I ++ [y])).IsChain R := hp.append_overlap hI (by simp)
  have h₂ : (A ++ [x] ++ I ++ [y] ++ B).IsChain R :=
    (show (A ++ [x] ++ I ++ [y]).IsChain R by simpa only [List.append_assoc] using h₁).append_overlap
      hs (by simp)
  simpa only [List.append_assoc, List.singleton_append] using h₂

theorem PathSystem.insert_step {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.edgeCount = P.edgeCount := by
  classical
  let D := P.chains.erase c
  let J := A ++ x :: I ++ y :: B
  have hp : P.chains.Perm (c :: D) := List.perm_cons_erase hc
  have hj : (J ++ D.flatten).Perm (I ++ P.chains.flatten) := by
    apply List.Perm.trans _ (hp.flatten.symm.append_left I)
    simp only [List.flatten_cons, he, J]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
    ac_nf
    exact Multiset.cons_swap ..
  have hnd : (J ++ D.flatten).Nodup := hj.nodup_iff.mpr
    (List.nodup_append.mpr ⟨hIn, P.nodup, fun a ha b hb hab =>
      List.disjoint_left.mp hId ha (hab ▸ hb)⟩)
  have hje : (∀ a ∈ J.head?, a ∈ Q) ∧ ∀ a ∈ J.getLast?, a ∈ Q := by
    have hh := P.ends c hc
    constructor
    · simpa only [he, J, List.append_assoc, List.cons_append, List.head?_append, List.head?_cons] using hh.1
    · have hec : c = (A ++ [x]) ++ y :: B := by simp only [he, List.append_assoc, List.singleton_append]
      have hej : J = (A ++ [x] ++ I) ++ y :: B := by
        simp only [J, List.append_assoc, List.cons_append, List.nil_append]
      simpa only [hec, hej, List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using hh.2
  let R : PathSystem G Q :=
    { chains := J :: D
      nonempty := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · simp [J]
        · exact P.nonempty d (List.mem_of_mem_erase hd)
      nodup := hnd
      edges := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.edges c hc) hI
        · exact P.edges d (List.mem_of_mem_erase hd)
      positive := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.positive c hc) hIp
        · exact P.positive d (List.mem_of_mem_erase hd)
      ends := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hje
        · exact P.ends d (List.mem_of_mem_erase hd)
      cover := by
        intro a ha
        exact hj.mem_iff.mpr (List.mem_append_right _ (P.cover a ha)) }
  refine ⟨R, ?_, ?_⟩
  · have hh := hj.length_eq
    simp only [List.length_append, P.flat_length] at hh
    change (J ++ D.flatten).length - Q.ncard = P.amount + I.length
    rw [List.length_append]
    omega
  · have hh := hp.length_eq
    change Q.ncard - (J :: D).length = Q.ncard - P.chains.length
    simp only [List.length_cons] at hh ⊢
    omega

theorem PathSystem.no_one_consecutive {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hk : 3 ≤ k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (ht : Q.ncard ≤ k)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A B : List V)
    (he : c = A ++ x :: y :: B) :
    ¬ OutsidePath G P.vertices x y 1 := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hIo⟩ := hp.to_list
  have hip : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) :=
    positive_interior_chain (by intro h; simp [h] at hIl)
      (fun a ha hQ => hIo a ha (P.cover a hQ))
  obtain ⟨R, hR, _⟩ := P.insert_step hc A I B he hI hip hIn (List.disjoint_left.mpr hIo)
  have hr : R.incident ≤ Q.ncard := Nat.sub_le _ _
  have hh := hopt.1
  apply P.optimality hopt hk hQ hcycle ht R (by omega) (by omega)
  omega

theorem PathSystem.representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.representatives.ncard = Q.ncard := by
  classical
  have he : P.representatives = (↑P.reps.toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup (P.nodup.sublist P.reps_sublist),
    P.reps_length]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ChainRearrangement
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem ChainAmounts.join {V : Type*} {Q : Set V} {c I : List V} {A B : List ℕ}
    {y : V} {v : List V} (hc : ChainAmounts Q c A) (hd : ChainAmounts Q (y :: v) B)
    (hI : I ≠ []) (ho : ∀ z ∈ I, z ∉ Q) :
    ChainAmounts Q (c ++ I ++ (y :: v)) (A ++ I.length :: B) := by
  induction hc with
  | singleton x hx => simpa using ChainAmounts.step x y I v B hx hI ho hd
  | step x z J D C hx hJ hJo htail ih =>
    simpa only [List.cons_append, List.append_assoc] using
      ChainAmounts.step x z J (D ++ I ++ y :: v) (C ++ I.length :: B) hx hJ hJo ih

theorem ChainAmounts.reverse {V : Type*} {Q : Set V} {c : List V} {A : List ℕ}
    (hc : ChainAmounts Q c A) : ChainAmounts Q c.reverse A.reverse := by
  induction hc with
  | singleton x hx => simpa using ChainAmounts.singleton x hx
  | step x y I B A hx hI ho htail ih =>
    have hh := ih.join (ChainAmounts.singleton x hx)
      (List.reverse_ne_nil_iff.mpr hI) (by simpa using ho)
    simpa only [List.reverse_cons, List.reverse_append, List.length_reverse,
      List.append_assoc, List.append_nil] using hh

theorem AmountProfile.of_reordered {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {C : List (List V)} {D : List (List ℕ)}
    (hp : P.chains.Perm C) (hD : List.Forall₂ (ChainAmounts Q) C D) :
    AmountProfile P D.flatten := by
  obtain ⟨E, hE, hED⟩ := List.perm_comp_forall₂ hp hD
  exact ⟨E, hE, hED.flatten⟩

theorem ChainAmounts.forall₂_exists {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (C : List (List V)) (h : ∀ c ∈ C, ClosedChain G Q c) :
    ∃ D : List (List ℕ), List.Forall₂ (ChainAmounts Q) C D := by
  induction C with
  | nil => exact ⟨[], .nil⟩
  | cons c C ih =>
    obtain ⟨A, hA⟩ := ChainAmounts.exists c (h c (by simp))
    obtain ⟨D, hD⟩ := ih (fun d hd => h d (by simp [hd]))
    exact ⟨A :: D, .cons hA hD⟩

 
theorem AmountProfile.join_starts {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P R : PathSystem G Q) {x y : V} {u v I : List V} {D : List (List V)}
    (hP : P.chains.Perm ((x :: u) :: (y :: v) :: D))
    (hR : R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: D)
    (hI : I ≠ []) (ho : ∀ z ∈ I, z ∉ Q) :
    ∃ A : List ℕ, AmountProfile P A ∧ AmountProfile R (I.length :: A) := by
  have hC : ∀ c ∈ ((x :: u) :: (y :: v) :: D), ClosedChain G Q c :=
    fun c hc => P.closed_chain (hP.mem_iff.mpr hc)
  obtain ⟨A, hA⟩ := ChainAmounts.exists (x :: u) (hC _ (by simp))
  obtain ⟨B, hB⟩ := ChainAmounts.exists (y :: v) (hC _ (by simp))
  obtain ⟨E, hE⟩ := ChainAmounts.forall₂_exists D (fun c hc => hC _ (by simp [hc]))
  have hPp := AmountProfile.of_reordered P hP (.cons hA (.cons hB hE))
  refine ⟨A ++ B ++ E.flatten, by simpa only [List.flatten_cons, List.append_assoc] using hPp, ?_⟩
  have hr : List.Forall₂ (ChainAmounts Q) R.chains ((A.reverse ++ I.length :: B) :: E) := by
    rw [hR]
    exact .cons (hA.reverse.join hB hI ho) hE
  refine ⟨(A.reverse ++ I.length :: B) :: E, hr, ?_⟩
  simp only [List.flatten_cons]
  apply List.Perm.trans ((List.reverse_perm A).append_right (I.length :: B) |>.append_right E.flatten)
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]

theorem PathSystem.join_distinct_chains_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧
      R.chains = ((x :: u).reverse ++ I ++ (y :: v)) ::
      (prefixChains A ++ prefixChains B ++ D) := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: d :: D))
  have hdd := P.closed_chain (hP.mem_iff.mpr (by simp : d ∈ c :: d :: D))
  obtain ⟨hA, hu⟩ := hcc.cut hc hcutc
  obtain ⟨hB, hv⟩ := hdd.cut hd hcutd
  let C := prefixChains A ++ prefixChains B ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hA l hl
    · exact hB l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc, hd]
    simpa only [List.append_assoc] using perm_reorder_four A (x :: u) B (y :: v) D.flatten
  obtain ⟨R, hR, hRC⟩ := P.join_tails_exact C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
  exact ⟨R, hR, hRC⟩

theorem PathSystem.join_same_chain_exact {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧
      R.chains = ((x :: u).reverse ++ I ++ (y :: v)) :: (prefixChains A ++ D) := by
  have hcc := P.closed_chain (hP.mem_iff.mpr (by simp : c ∈ c :: D))
  obtain ⟨hA, hu⟩ := hcc.cut (by simpa only [List.append_assoc, List.cons_append] using hc) hcut
  have he : ((x :: u) ++ y :: v).IsChain G.Adj := by simpa only [List.cons_append] using hu.edges
  have hp : ((x :: u) ++ y :: v).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
    simpa only [List.cons_append] using hu.positive
  have hve : ∀ a ∈ (y :: v).getLast?, a ∈ Q := by
    simpa only [hc, List.getLast?_append_of_ne_nil _ (by simp : y :: v ≠ [])] using hcc.ends.2
  let C := prefixChains A ++ D
  have hC : ∀ l ∈ C, ClosedChain G Q l := by
    intro l hl
    simp only [C, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hA l hl
    · exact P.closed_chain (hP.mem_iff.mpr (by simp [hl]))
  have hperm : ((x :: u) ++ (y :: v) ++ C.flatten).Perm P.chains.flatten := by
    apply List.Perm.trans _ hP.flatten.symm
    simp only [C, List.flatten_append, prefixChains_flatten, List.flatten_cons, hc]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  obtain ⟨R, hR, hRC⟩ := P.join_tails_exact C u v I hperm
    (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
    (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
    he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
    hum hve hI hIp hIn hId
  exact ⟨R, hR, hRC⟩

theorem PathSystem.small_increment_run {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P R : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {I c : List V} (hI : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q)
    (hR : R.amount = P.amount + I.length) (he : R.edgeCount ≤ P.edgeCount + 1)
    (hc : c ∈ R.chains) (hin : I <:+: c) :
    P.amount = k - Q.ncard ∧ R.edgeCount = P.edgeCount + 1 ∧ 2 ≤ I.length := by
  obtain ⟨A, hA⟩ := R.exists_profile
  obtain ⟨b, hb, hbd⟩ := hA.run_bound hc hI hout hin
  have hd : 1 ≤ I.length := List.length_pos_iff.mpr hI
  obtain ⟨hL, heq, hd2, _⟩ := P.small_increment R hopt hQ hcycle ht htk hkt hd hI6 hR he hA hb hbd
  exact ⟨hL, heq, hd2⟩

theorem prefixChains_length_eq {V : Type*} (A : List V) :
    (prefixChains A).length = if A = [] then 0 else 1 := by
  by_cases h : A = [] <;> simp [prefixChains, h]

theorem PathSystem.short_distinct_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c d : List V} (D : List (List V)) (hP : P.chains.Perm (c :: d :: D))
    {x y : V} (A u B v I : List V) (hc : c = A ++ x :: u) (hd : d = B ++ y :: v)
    (hcutc : MarkedCut Q true A) (hcutd : MarkedCut Q true B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) :
    A = [] ∧ B = [] ∧ P.amount = k - Q.ncard ∧ 2 ≤ I.length ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length ∧
      ∃ F : List ℕ, AmountProfile P F ∧ ∀ a ∈ F, I.length ≤ a := by
  classical
  obtain ⟨R, hR, hRC⟩ := P.join_distinct_chains_exact D hP A u B v I hc hd hcutc hcutd
    hI hIp hIn hId
  have hPC := hP.length_eq
  simp only [List.length_cons] at hPC
  have hRCn := congrArg List.length hRC
  simp only [List.length_cons, List.length_append, prefixChains_length_eq] at hRCn
  have hPle := P.chains_length_le
  have hRle := R.chains_length_le
  have he : R.edgeCount ≤ P.edgeCount + 1 := by dsimp [PathSystem.edgeCount]; omega
  have hr := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR he
    (by rw [hRC]; simp) (show I <:+: (x :: u).reverse ++ I ++ y :: v from
      ⟨(x :: u).reverse, y :: v, rfl⟩)
  have hAB : A = [] ∧ B = [] := by
    have heq := hr.2.1
    dsimp [PathSystem.edgeCount] at heq
    split_ifs at hRCn <;> first | (constructor <;> assumption) | omega
  obtain ⟨rfl, rfl⟩ := hAB
  simp only [List.nil_append] at hc hd
  subst c d
  simp only [prefixChains, ite_true, if_true, List.nil_append] at hRC
  obtain ⟨F, hF, hRF⟩ := AmountProfile.join_starts P R hP hRC hI0 hout
  obtain ⟨hL, heq, hd2, hge⟩ := P.small_increment R hopt hQ hcycle ht htk hkt
    (List.length_pos_iff.mpr hI0) hI6 hR he hRF (by simp) (le_refl _)
  have hJlen : (((x :: u).reverse ++ I ++ y :: v)).length ≠ 1 := by simp; omega
  have hsing : R.singletons.length = (D.filter (fun c => c.length = 1)).length := by
    simp only [PathSystem.singletons, hRC, List.filter_cons, hJlen, decide_false, Bool.false_eq_true, ite_false, if_false]
  have hi : k + 1 - R.incident < R.amount := by
    by_contra! hi
    exact R.closing_interval (by omega) hQ hcycle htk (by omega) hi
  have hsle := R.singletons_length_le
  have hcount : (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length := by
    dsimp [PathSystem.incident] at hi
    omega
  exact ⟨rfl, rfl, hL, hd2, hcount, F, hF, fun a ha => hge a (by simp [ha])⟩

theorem PathSystem.not_short_same_chain {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c : List V} (D : List (List V)) (hP : P.chains.Perm (c :: D))
    {x y : V} (A u v I : List V) (hc : c = A ++ (x :: u) ++ y :: v)
    (hcut : MarkedCut Q true A) (hum : ∀ a ∈ (x :: u).getLast?, a ∈ Q)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) : False := by
  obtain ⟨R, hR, hRC⟩ := P.join_same_chain_exact D hP A u v I hc hcut hum hI hIp hIn hId
  have hPC := hP.length_eq
  simp only [List.length_cons] at hPC
  have hRCn := congrArg List.length hRC
  simp only [List.length_cons, List.length_append, prefixChains_length_eq] at hRCn
  have hPle := P.chains_length_le
  have he : R.edgeCount ≤ P.edgeCount := by dsimp [PathSystem.edgeCount]; omega
  have hr := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega)
    (by rw [hRC]; simp) (show I <:+: (x :: u).reverse ++ I ++ y :: v from
      ⟨(x :: u).reverse, y :: v, rfl⟩)
  omega

theorem PathSystem.insert_step_run {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten) :
    ∃ R : PathSystem G Q, R.amount = P.amount + I.length ∧ R.edgeCount = P.edgeCount ∧ ∃ c ∈ R.chains, I <:+: c := by
  classical
  let D := P.chains.erase c
  let J := A ++ x :: I ++ y :: B
  have hp : P.chains.Perm (c :: D) := List.perm_cons_erase hc
  have hj : (J ++ D.flatten).Perm (I ++ P.chains.flatten) := by
    apply List.Perm.trans _ (hp.flatten.symm.append_left I)
    simp only [List.flatten_cons, he, J]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
    ac_nf
    exact Multiset.cons_swap ..
  have hnd : (J ++ D.flatten).Nodup := hj.nodup_iff.mpr
    (List.nodup_append.mpr ⟨hIn, P.nodup, fun a ha b hb hab =>
      List.disjoint_left.mp hId ha (hab ▸ hb)⟩)
  have hje : (∀ a ∈ J.head?, a ∈ Q) ∧ ∀ a ∈ J.getLast?, a ∈ Q := by
    have hh := P.ends c hc
    constructor
    · simpa only [he, J, List.append_assoc, List.cons_append, List.head?_append, List.head?_cons] using hh.1
    · have hec : c = (A ++ [x]) ++ y :: B := by simp only [he, List.append_assoc, List.singleton_append]
      have hej : J = (A ++ [x] ++ I) ++ y :: B := by
        simp only [J, List.append_assoc, List.cons_append, List.nil_append]
      simpa only [hec, hej, List.getLast?_append_of_ne_nil _ (by simp : y :: B ≠ [])] using hh.2
  let R : PathSystem G Q :=
    { chains := J :: D
      nonempty := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · simp [J]
        · exact P.nonempty d (List.mem_of_mem_erase hd)
      nodup := hnd
      edges := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.edges c hc) hI
        · exact P.edges d (List.mem_of_mem_erase hd)
      positive := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact isChain_insert_step (he ▸ P.positive c hc) hIp
        · exact P.positive d (List.mem_of_mem_erase hd)
      ends := by
        intro d hd
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hje
        · exact P.ends d (List.mem_of_mem_erase hd)
      cover := by
        intro a ha
        exact hj.mem_iff.mpr (List.mem_append_right _ (P.cover a ha)) }
  refine ⟨R, ?_, ?_, J, by simp [R], (A ++ [x]), y :: B, ?_⟩
  · have hh := hj.length_eq
    simp only [List.length_append, P.flat_length] at hh
    change (J ++ D.flatten).length - Q.ncard = P.amount + I.length
    rw [List.length_append]
    omega
  · have hh := hp.length_eq
    change Q.ncard - (J :: D).length = Q.ncard - P.chains.length
    simp only [List.length_cons] at hh ⊢
    omega
  · simp only [J, List.append_assoc, List.cons_append, List.nil_append]

theorem PathSystem.short_representatives {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxy : x ≠ y) (I : List V)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) :
    ∃ u v : List V, ∃ D : List (List V), ∃ F : List ℕ,
      P.chains.Perm ((x :: u) :: (y :: v) :: D) ∧
      P.amount = k - Q.ncard ∧ 2 ≤ I.length ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ I.length ∧
      AmountProfile P F ∧ ∀ a ∈ F, I.length ≤ a := by
  classical
  obtain ⟨rc, hrc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
  obtain ⟨rd, hrd, hyd⟩ := List.mem_flatten.mp hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrd
  have hnc := (List.nodup_flatten.mp P.nodup).1 c hc
  by_cases hcd : c = d
  · subst d
    have hp := List.perm_cons_erase hc
    rcases two_mem_ordered ((markedReps_sublist Q true c).subset hxc)
      ((markedReps_sublist Q true c).subset hyd) hxy with hh | hh
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hxc hyd A u v he
      exact (P.not_short_same_chain hopt hQ hcycle ht htk hkt
        (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId hI0 hI6 hout).elim
    · obtain ⟨A, u, v, he⟩ := hh
      obtain ⟨hA, hu⟩ := markedCuts_ordered hnc hyd hxc A u v he
      have hi : (y :: I.reverse ++ [x]).IsChain G.Adj := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hI.imp (fun _ _ h => h.symm))
      have hip : (y :: I.reverse ++ [x]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q) := by
        simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.append_assoc, List.reverse_nil, List.nil_append, List.cons_append] using
          List.isChain_reverse.mpr (hIp.imp (fun _ _ h => h.symm))
      exact (P.not_short_same_chain hopt hQ hcycle ht htk hkt
        (P.chains.erase c) hp A u v I.reverse he hA hu hi hip (by simpa using hIn)
        (by simpa using hId) (by simpa using hI0) (by simpa using hI6) (by simpa using hout)).elim
  · have hp₁ := List.perm_cons_erase hc
    have hd' : d ∈ P.chains.erase c := (List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
    have hp₂ := List.perm_cons_erase hd'
    have hp := hp₁.trans (hp₂.cons c)
    obtain ⟨A, u, hec, hcutc⟩ := (mem_markedReps Q true c x).mp hxc
    obtain ⟨B, v, hed, hcutd⟩ := (mem_markedReps Q true d y).mp hyd
    obtain ⟨rfl, rfl, hL, hd2, hS, F, hF, hFa⟩ :=
      P.short_distinct_chains hopt hQ hcycle ht htk hkt ((P.chains.erase c).erase d)
        hp A u B v I hec hed hcutc hcutd hI hIp hIn hId hI0 hI6 hout
    simp only [List.nil_append] at hec hed
    exact ⟨u, v, (P.chains.erase c).erase d, F, by simpa [← hec, ← hed] using hp,
      hL, hd2, hS, hF, hFa⟩

theorem PathSystem.not_short_consecutive {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k : ℕ} (P : PathSystem G Q)
    (hopt : P.Optimal k) (hQ : G.IsClique Q)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (ht : 9 ≤ Q.ncard) (htk : Q.ncard ≤ k) (hkt : k ≤ 2 * Q.ncard + 1)
    {c : List V} (hc : c ∈ P.chains) {x y : V} (A I B : List V)
    (he : c = A ++ x :: y :: B)
    (hI : (x :: I ++ [y]).IsChain G.Adj)
    (hIp : (x :: I ++ [y]).IsChain (fun a b => a ∉ Q ∨ b ∉ Q))
    (hIn : I.Nodup) (hId : I.Disjoint P.chains.flatten)
    (hI0 : I ≠ []) (hI6 : I.length ≤ 6) (hout : ∀ z ∈ I, z ∉ Q) : False := by
  obtain ⟨R, hR, heR, cR, hcR, hiR⟩ := P.insert_step_run hc A I B he hI hIp hIn hId
  have hh := P.small_increment_run R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega) hcR hiR
  omega

theorem PathSystem.orient_perm {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).chains.flatten.Perm P.chains.flatten := flipChains_flatten_perm f P.chains

@[simp] theorem PathSystem.orient_amount {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) :
    (P.orient f).amount = P.amount := by
  change (P.orient f).chains.flatten.length - Q.ncard = P.chains.flatten.length - Q.ncard
  rw [(P.orient_perm f).length_eq]

@[simp] theorem PathSystem.orient_optimal {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (f : List V → Bool) {k : ℕ} :
    (P.orient f).Optimal k ↔ P.Optimal k := by simp [PathSystem.Optimal]

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ExteriorBalls
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem closedNeighborhood_mono {V : Type*} (G : SimpleGraph V) {A B : Set V}
    (h : A ⊆ B) : closedNeighborhood G A ⊆ closedNeighborhood G B := by
  rintro v (hv | ⟨u, hu, huv⟩)
  · exact Or.inl (h hv)
  · exact Or.inr ⟨u, h hu, huv⟩

theorem outside_neighborhood_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X Z A : Set V} {x : V} {r : ℕ}
    (hA : A ⊆ outsideBall G X x r) (hZ : Z ⊆ X)
    (hmiss : ∀ u ∈ A, ∀ z ∈ Z, ¬ G.Adj u z) :
    (closedNeighborhood G A).ncard + Z.ncard ≤
      X.ncard + (outsideBall G X x (r + 1)).ncard := by
  have hdis : Disjoint (closedNeighborhood G A) Z := by
    apply Set.disjoint_left.mpr
    rintro z (hz | ⟨u, hu, huz⟩) hzZ
    · exact outsideBall_subset_compl G X x r (hA hz) (hZ hzZ)
    · exact hmiss u hu z hzZ huz
  have hs : closedNeighborhood G A ⊆ outsideBall G X x (r + 1) ∪ (X \ Z) := by
    intro z hz
    rcases closedNeighborhood_ball_subset G X x r (closedNeighborhood_mono G hA hz) with hb | hx
    · exact Or.inl hb
    · exact Or.inr ⟨hx, fun hzZ => Set.disjoint_left.mp hdis hz hzZ⟩
  have hc := Set.ncard_le_ncard hs
  have hu := Set.ncard_union_le (outsideBall G X x (r + 1)) (X \ Z)
  have hd := Set.ncard_sdiff_add_ncard_of_subset hZ
  omega

theorem outsideBall_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X : Set V} {x : V} {k : ℕ}
    (hx : x ∈ X) (hX : X.ncard ≤ k)
    (hdeg : k + 1 ≤ (closedNeighborhood G {x}).ncard) :
    (outsideBall G X x 0).Nonempty := by
  by_contra hn
  have hs : closedNeighborhood G {x} ⊆ X := by
    rintro v (hv | ⟨u, hu, huv⟩)
    · simpa using (Set.mem_singleton_iff.mp hv ▸ hx)
    · have he : u = x := hu
      subst u
      by_contra hvX
      exact hn ⟨v, huv, hvX⟩
  have hh := Set.ncard_le_ncard hs
  omega

theorem outsideBall_degree_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X Z : Set V} {x : V} {k : ℕ}
    (hx : x ∈ X) (hX : X.ncard ≤ k) (hZ : Z ⊆ X)
    (hdeg : ∀ u, k + 1 ≤ (closedNeighborhood G {u}).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 0, ∀ z ∈ Z, ¬ G.Adj u z) :
    k + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x 1).ncard := by
  obtain ⟨u, hu⟩ := outsideBall_nonempty hx hX (hdeg x)
  have hc := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hu) hZ
    (by intro v hv; have he : v = u := hv; subst v; exact hmiss u hu)
  have hd := hdeg u
  change (closedNeighborhood G {u}).ncard + Z.ncard ≤ X.ncard + (outsideBall G X x 1).ncard at hc
  omega

theorem outsideBall_independent_pair {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X R : Set V} {x : V} {k t : ℕ}
    (hR : R ⊆ X) (hx : x ∈ R) (hcardR : R.ncard = t) (hX : X.ncard ≤ k)
    (hclique : G.cliqueNum ≤ t)
    (hdeg : ∀ u, k + 1 ≤ (closedNeighborhood G {u}).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 1, ∀ z ∈ R \ {x}, ¬ G.Adj u z) :
    2 ≤ independence G (outsideBall G X x 2) := by
  have ht : 1 ≤ t := by
    have hp := (Set.ncard_pos).mpr (show R.Nonempty from ⟨x, hx⟩)
    omega
  have hZ : R \ {x} ⊆ X := Set.sdiff_subset.trans hR
  have hcZ : (R \ {x}).ncard = t - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hcardR]
  have hb := outsideBall_degree_bound (hR hx) hX hZ hdeg
    (fun u hu => hmiss u (outsideBall_subset_succ G X x 0 hu))
  rw [hcZ] at hb
  by_contra hn
  have htwo : G.IsClique (outsideBall G X x 2) := clique_of_independence_le_one (by omega)
  have hc2 := (clique_ncard_le_cliqueNum htwo).trans hclique
  have hsub := outsideBall_subset_succ G X x 1
  have hc12 : (outsideBall G X x 1).ncard ≤ (outsideBall G X x 2).ncard := Set.ncard_le_ncard hsub
  have hc1 : (outsideBall G X x 1).ncard = t := by omega
  have hadj : ∀ z ∈ outsideBall G X x 1, G.Adj x z := by
    intro z hz
    by_contra hneg
    have hmissR : ∀ u ∈ ({z} : Set V), ∀ w ∈ R, ¬ G.Adj u w := by
      intro u hu w hw huw
      have he : u = z := hu
      subst u
      by_cases hwx : w = x
      · subst w
        exact hneg huw.symm
      · exact hmiss z hz w ⟨hw, hwx⟩ huw
    have hh := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hz) hR hmissR
    rw [hcardR] at hh
    change (closedNeighborhood G {z}).ncard + t ≤ X.ncard + (outsideBall G X x 2).ncard at hh
    have hd := hdeg z
    omega
  have hxB : x ∉ outsideBall G X x 1 := fun hh =>
    outsideBall_subset_compl G X x 1 hh (hR hx)
  have hbig : G.IsClique (insert x (outsideBall G X x 1)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hadj v hv
    · exact (hadj u hu).symm
    · exact htwo (hsub hu) (hsub hv) huv
  have hc := (clique_ncard_le_cliqueNum hbig).trans hclique
  rw [Set.ncard_insert_of_notMem hxB, hc1] at hc
  omega

theorem outsideBall_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {X R : Set V} {x : V} {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (htk : t < k)
    (hR : R ⊆ X) (hx : x ∈ R) (hcardR : R.ncard = t) (hX : X.ncard ≤ k)
    (hclique : G.cliqueNum ≤ t) (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G)
    (hexp : ∀ I : Set V, G.IsIndepSet I → I.Nonempty →
      k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard)
    (hmiss : ∀ u ∈ outsideBall G X x 1, ∀ z ∈ R \ {x}, ¬ G.Adj u z)
    (hnclique : ¬ G.IsClique (outsideBall G X x 1)) :
    3 ≤ independence G (outsideBall G X x 2) := by
  have ha : 2 ≤ independence G (outsideBall G X x 1) := by
    by_contra hn
    exact hnclique (clique_of_independence_le_one (by omega))
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G X x 1)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := hexp I hI hIn
  have hb := outside_neighborhood_bound hIs (Set.sdiff_subset.trans hR)
    (fun u hu => hmiss u (hIs hu))
  have hcZ : (R \ {x}).ncard = t - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hx, hcardR]
  rw [hcZ] at hb
  change (closedNeighborhood G I).ncard + (t - 1) ≤ X.ncard + (outsideBall G X x 2).ncard at hb
  have hm : 2 * k ≤ k * I.ncard := by
    have hh := Nat.mul_le_mul_left k (show 2 ≤ I.ncard by omega)
    simpa only [Nat.mul_comm k 2] using hh
  apply size_test hk ht hcycle hclique
  omega

theorem outsideBall_misses_representatives {V : Type*} {G : SimpleGraph V}
    {X R : Set V} {x : V} {r : ℕ} (hR : R ⊆ X) (hx : x ∈ R)
    (hno : ∀ y ∈ R, ∀ d, 1 ≤ d → d ≤ r + 1 → ¬ OutsidePath G X x y d) :
    ∀ u ∈ outsideBall G X x r, ∀ z ∈ R \ {x}, ¬ G.Adj u z := by
  intro u hu z hz
  exact outside_ball_misses (hR hx) (hR hz.1) (Ne.symm hz.2)
    (fun d hd hd' => hno z hz.1 d hd hd') u hu

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LargeSystems
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

theorem PathSystem.chains_nodup {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.chains.Nodup := by
  apply (List.nodup_flatten.mp P.nodup).2.imp_of_mem
  intro a b ha hb hd heq
  subst b
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil a (P.nonempty a ha)
  exact List.disjoint_left.mp hd hx hx

theorem PathSystem.incident_eq_edges_add_chains {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident = P.edgeCount + P.usedChains.length := by
  have hh := P.partition.length_eq
  simp only [List.length_append] at hh
  have hle := P.chains_length_le
  dsimp [PathSystem.incident, PathSystem.edgeCount]
  omega

theorem PathSystem.rep_of_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V}
    (hx : x ∈ markedReps Q true c) : x ∈ P.reps := by
  exact List.mem_flatten.mpr ⟨markedReps Q true c, List.mem_map.mpr ⟨c, hc, rfl⟩, hx⟩

theorem PathSystem.rep_iff_in_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V} (hx : x ∈ c) :
    x ∈ P.reps ↔ x ∈ markedReps Q true c := by
  classical
  refine ⟨?_, P.rep_of_chain hc⟩
  intro hxr
  have hp := List.perm_cons_erase hc
  have hnd : (c ++ (P.chains.erase c).flatten).Nodup := hp.flatten.nodup_iff.mp P.nodup
  have hrp := (hp.map (markedReps Q true)).flatten
  have hv := hrp.mem_iff.mp hxr
  simp only [List.map_cons, List.flatten_cons, List.mem_append] at hv
  rcases hv with hv | hv
  · exact hv
  · exact ((List.nodup_append.mp hnd).2.2 x hx x
      ((markedReps_flatten_sublist Q _).subset hv) rfl).elim

theorem ClosedChain.rep_mem_Q_iff_head {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c : List V} (hc : ClosedChain G Q c) {x : V} (hx : x ∈ Q) :
    x ∈ markedReps Q true c ↔ x ∈ c.head? := by
  classical
  constructor
  · intro hrep
    obtain ⟨A, B, he, hcut⟩ := (mem_markedReps Q true c x).mp hrep
    rcases hcut with ⟨rfl, _⟩ | ⟨hne, hend⟩
    · simp [he]
    · have hp := List.isChain_append.mp (he ▸ hc.positive)
      have hla : A.getLast hne ∈ A.getLast? := List.getLast?_eq_some_getLast hne
      exact ((hp.2.2 _ hla x (by simp)).elim (fun h => h (hend _ hla)) (fun h => h hx)).elim
  · intro hh
    cases c with
    | nil => simp at hh
    | cons y B =>
      have he : y = x := by simpa using hh
      subst y
      simp [markedReps]

theorem PathSystem.interior_rep_next {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {x : V} (hx : x ∈ P.reps) (hxQ : x ∉ Q) :
    ∃ c ∈ P.chains, ∃ A B : List V, ∃ y : V,
      c = A ++ x :: y :: B ∧ y ∉ P.reps := by
  obtain ⟨rc, hrc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrc
  obtain ⟨A, B, he, hcut⟩ := (mem_markedReps Q true c x).mp hxc
  have hnB : B ≠ [] := by
    intro hb
    have hxend : x ∈ c.getLast? := by simp [he, hb]
    exact hxQ ((P.ends c hc).2 x hxend)
  obtain ⟨y, D, hB⟩ := List.exists_cons_of_ne_nil hnB
  subst B
  refine ⟨c, hc, A, D, y, he, ?_⟩
  intro hy
  have hyc : y ∈ c := by simp [he]
  have hyrep := (P.rep_iff_in_chain hc hyc).mp hy
  have hnc := (List.nodup_flatten.mp P.nodup).1 c hc
  have hcuty := markedCut_of_split hnc hyrep (show c = (A ++ [x]) ++ y :: D by
    simpa only [List.append_assoc, List.singleton_append] using he)
  rcases hcuty with ⟨hempty, _⟩ | ⟨_, hlast⟩
  · simp at hempty
  · exact hxQ (hlast x (by simp))

theorem ClosedChain.reps_Q_count {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {c : List V} (hc : ClosedChain G Q c) (hn : c.Nodup) :
    (markedReps Q true c).countP (fun x => decide (x ∈ Q)) = 1 := by
  classical
  let x := c.head hc.nonempty
  have hxQ : x ∈ Q := hc.ends.1 x (List.head?_eq_some_head _)
  have he : ((markedReps Q true c).filter (fun x => decide (x ∈ Q))).toFinset = {x} := by
    ext y
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hyQ⟩
      have hh := hc.rep_mem_Q_iff_head hyQ |>.mp hy
      simpa only [List.head?_eq_some_head hc.nonempty, Option.mem_def, Option.some.injEq] using hh.symm
    · rintro rfl
      exact ⟨(hc.rep_mem_Q_iff_head hxQ).mpr (List.head?_eq_some_head _), hxQ⟩
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    (((markedReps_sublist Q true c).nodup hn).filter _), he]
  simp

theorem PathSystem.reps_Q_count {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.reps.countP (fun x => decide (x ∈ Q)) = P.chains.length := by
  classical
  simp only [PathSystem.reps, List.countP_flatten, List.map_map]
  have hm : P.chains.map (fun c => (markedReps Q true c).countP (fun x => decide (x ∈ Q))) =
      P.chains.map (fun _ => 1) := by
    apply List.map_congr_left
    intro c hc
    exact (P.closed_chain hc).reps_Q_count ((List.nodup_flatten.mp P.nodup).1 c hc)
  simp only [Function.comp_def]
  rw [hm]
  simp

theorem PathSystem.interior_reps_length {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.reps.filter (fun x => x ∉ Q)).length = P.edgeCount := by
  classical
  have hh := P.reps.length_eq_countP_add_countP (fun x => decide (x ∈ Q))
  rw [P.reps_Q_count, P.reps_length] at hh
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, List.countP_eq_length_filter] at hh
  dsimp [PathSystem.edgeCount]
  omega

theorem PathSystem.chains_disjoint {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c d : List V} (hc : c ∈ P.chains) (hd : d ∈ P.chains) (hne : c ≠ d) :
    c.Disjoint d := by
  classical
  have hp := List.perm_cons_erase hc
  have hnd : (c ++ (P.chains.erase c).flatten).Nodup := hp.flatten.nodup_iff.mp P.nodup
  apply List.disjoint_left.mpr
  intro x hx hy
  exact (List.nodup_append.mp hnd).2.2 x hx x
    (List.mem_flatten.mpr ⟨d, (List.mem_erase_of_ne (Ne.symm hne)).mpr hd, hy⟩) rfl

theorem markedReps_head {V : Type*} (Q : Set V) {c : List V} (hn : c ≠ []) :
    c.head hn ∈ markedReps Q true c := by
  cases c with
  | nil => contradiction
  | cons x c => simp [markedReps]

theorem PathSystem.reverse_other_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) (hc1 : c.length ≠ 1)
    {x : V} (hx : x ∈ P.reps) (hxc : x ∉ c) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  let f : List V → Bool := fun d => decide (d = c)
  let y := c.getLast (P.nonempty c hc)
  have hyc : y ∈ c := List.getLast_mem _
  have hyQ : y ∈ Q := (P.ends c hc).2 y (List.getLast?_eq_some_getLast _)
  have hyR : y ∉ P.reps := by
    intro hy
    have hh := (P.closed_chain hc).rep_mem_Q_iff_head hyQ |>.mp ((P.rep_iff_in_chain hc hyc).mp hy)
    have hhe : c.head (P.nonempty c hc) = c.getLast (P.nonempty c hc) := by
      simpa only [List.head?_eq_some_head (P.nonempty c hc), Option.mem_def, Option.some.injEq] using hh
    obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff (P.nonempty c hc)
      ((List.nodup_flatten.mp P.nodup).1 c hc)).mp hhe
    exact hc1 (by simp [hz])
  have hxnew : x ∈ (P.orient f).reps := by
    obtain ⟨rc, hrc, hxr⟩ := List.mem_flatten.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hrc
    have hdc : d ≠ c := by
      intro he
      subst d
      exact hxc ((markedReps_sublist Q true c).subset hxr)
    have hdnew : d ∈ (P.orient f).chains := by
      rw [orient_chains]
      exact List.mem_map.mpr ⟨d, hd, by simp [f, flipChain, hdc]⟩
    exact (P.orient f).rep_of_chain hdnew hxr
  have hcnew : c.reverse ∈ (P.orient f).chains := by
    rw [orient_chains]
    exact List.mem_map.mpr ⟨c, hc, by simp [f, flipChain]⟩
  have hynew : y ∈ (P.orient f).reps := by
    apply (P.orient f).rep_of_chain hcnew
    have hh := markedReps_head Q (show c.reverse ≠ [] by simpa using P.nonempty c hc)
    simpa using hh
  exact ⟨f, y, List.mem_flatten.mpr ⟨c, hc, hyc⟩, hyR, hxnew, hynew⟩

theorem list_two_ne {α : Type*} {l : List α} (hn : l.Nodup) (hl : 2 ≤ l.length) (a : α) :
    ∃ b ∈ l, b ≠ a := by
  cases l with
  | nil => simp at hl
  | cons b l =>
    cases l with
    | nil => simp at hl
    | cons c l =>
      have hbc : b ≠ c := by
        intro he
        exact (List.nodup_cons.mp hn).1 (by simp [he])
      by_cases hba : b = a
      · exact ⟨c, by simp, by intro he; exact hbc (hba.trans he.symm)⟩
      · exact ⟨b, by simp, hba⟩

theorem PathSystem.extra_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (hu : 2 ≤ P.usedChains.length) {x : V} (hx : x ∈ P.reps) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  obtain ⟨d, hd, hxd⟩ := List.mem_flatten.mp (P.reps_sublist.subset hx)
  obtain ⟨c, hc, hcd⟩ := list_two_ne (P.chains_nodup.filter _) hu d
  have hc' : c ∈ P.chains ∧ c.length ≠ 1 := by simpa [PathSystem.usedChains] using hc
  exact P.reverse_other_rep hc'.1 hc'.2 hx (fun hxc =>
    List.disjoint_left.mp (P.chains_disjoint hc'.1 hd hcd) hxc hxd)

theorem terminal_classification_numeric {t k L e v d : ℕ}
    (ht : 9 ≤ t) (hkt : k ≤ 2*t+1) (hL : L + t = k)
    (hve : v ≤ 2*e) (hdL : d*e ≤ L) (htv : t ≤ v+d)
    (hd : 2 ≤ d) (hd6 : d ≤ 6) :
    (d = 2 ∧ t ≤ v + 2) ∨
    (d = 3 ∧ ((t = 9 ∧ e = 3 ∧ v = 6) ∨ (t = 11 ∧ e = 4 ∧ v = 8))) ∨
    (d = 5 ∧ t = 9 ∧ k = 19 ∧ e = 2 ∧ v = 4) := by
  interval_cases d
  · exact Or.inl ⟨rfl, htv⟩
  · have htt : t ≤ 11 := by nlinarith
    interval_cases t
    · exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, by omega, by omega⟩⟩)
    · omega
    · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, by omega, by omega⟩⟩)
  · have htt : t ≤ 9 := by nlinarith
    omega
  · have htt : t ≤ 9 := by nlinarith
    exact Or.inr (Or.inr ⟨rfl, by omega, by omega, by omega, by omega⟩)
  · have htt : t ≤ 9 := by nlinarith
    omega

@[simp] theorem PathSystem.orient_vertices {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) : (P.orient f).vertices = P.vertices := by
  ext x
  exact (P.orient_perm f).mem_iff

theorem PathSystem.representatives_subset {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.representatives ⊆ P.vertices := P.reps_sublist.subset



namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem degree (x : V) : k + 1 ≤ (closedNeighborhood G {x}).ncard := by
  simpa using H.expansion {x} (by simp) (Set.singleton_nonempty x)

 theorem vertices_le : P.vertices.ncard ≤ k := by
  rw [P.vertices_ncard]
  have hh := H.optimal.1
  have hk := H.le_k
  omega

 theorem orient (f : List V → Bool) : LargeSystem G Q k (P.orient f) :=
  ⟨(P.orient_optimal f).mpr H.optimal, H.clique, H.no_cycle, H.nine, H.le_k,
    H.k_le, H.maximal, H.independent, H.expansion⟩

 theorem no_one {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) :
    ¬ OutsidePath G P.vertices x y 1 :=
  P.no_one_representatives H.optimal (by have := H.nine; have := H.le_k; omega)
    H.clique H.no_cycle H.le_k hx hy

 theorem misses_reps {x : V} (hx : x ∈ P.reps) :
    ∀ u ∈ outsideBall G P.vertices x 0, ∀ z ∈ P.representatives \ {x}, ¬ G.Adj u z := by
  apply outsideBall_misses_representatives P.representatives_subset hx
  intro y hy d hd hd'
  have he : d = 1 := by omega
  subst d
  exact H.no_one hx hy

 theorem extra_degree {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.vertices)
    (hyR : y ∉ P.reps)
    (hmiss : ∀ u ∈ outsideBall G P.vertices x 0, ¬ G.Adj u y) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  let Z := insert y (P.representatives \ {x})
  have ht : 1 ≤ Q.ncard := by have := H.nine; omega
  have hc : Z.ncard = Q.ncard := by
    rw [Set.ncard_insert_of_notMem (by exact fun h => hyR h.1),
      Set.ncard_sdiff_singleton_of_mem (show x ∈ P.representatives from hx), P.representatives_ncard]
    omega
  have hZ : Z ⊆ P.vertices := by
    intro z hz
    rcases hz with rfl | hz
    · exact hy
    · exact P.representatives_subset hz.1
  have hb := outsideBall_degree_bound (P.representatives_subset hx) H.vertices_le hZ H.degree
    (by
      intro u hu z hz
      rcases hz with rfl | hz
      · exact hmiss u hu
      · exact H.misses_reps hx u hu z hz)
  rw [hc] at hb
  have hs := H.vertices_le
  omega

 theorem interior_degree {x : V} (hx : x ∈ P.reps) (hxQ : x ∉ Q) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  obtain ⟨c, hc, A, B, y, he, hyR⟩ := P.interior_rep_next hx hxQ
  have hy : y ∈ P.vertices := List.mem_flatten.mpr ⟨c, hc, by simp [he]⟩
  apply H.extra_degree hx hy hyR
  apply outside_ball_misses (P.representatives_subset hx) hy
    (by intro heq; exact hyR (heq ▸ hx))
  intro d hd hd'
  have hd1 : d = 1 := by omega
  subst d
  exact P.no_one_consecutive H.optimal (by have := H.nine; have := H.le_k; omega)
    H.clique H.no_cycle H.le_k hc A B he

 theorem reverse_degree {x : V} (hx : x ∈ P.reps)
    (he : ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
  obtain ⟨f, y, hy, hyR, hx', hy'⟩ := he
  apply H.extra_degree hx hy hyR
  apply outside_ball_misses (P.representatives_subset hx) hy
    (by intro heq; exact hyR (heq ▸ hx))
  intro d hd hd'
  have hd1 : d = 1 := by omega
  subst d
  simpa using (H.orient f).no_one hx' hy'

 theorem two_chains_degree (hu : 2 ≤ P.usedChains.length) {x : V} (hx : x ∈ P.reps) :
    Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard :=
  H.reverse_degree hx (P.extra_rep hu hx)

 theorem first_nonclique {x : V} (hb : Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard) :
    ¬ G.IsClique (outsideBall G P.vertices x 1) := by
  intro hc
  have hh := (clique_ncard_le_cliqueNum hc).trans H.maximal
  omega

 theorem first_pair {x : V} (hb : Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard) :
    2 ≤ independence G (outsideBall G P.vertices x 1) := by
  by_contra! hn
  exact H.first_nonclique hb (clique_of_independence_le_one (by omega))

end LargeSystem

 

theorem sum_independence_local {V : Type*} [Fintype V] {ι : Type*}
    (G : SimpleGraph V) (D : ι → Set V) (F : Finset ι)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (D i) (D j))
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      ∀ x ∈ D i, ∀ y ∈ D j, ¬ G.Adj x y) :
    ∑ i ∈ F, independence G (D i) ≤ G.indepNum := by
  classical
  have hh : ∑ i ∈ F, independence G (D i) ≤ independence G (⋃ i ∈ F, D i) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
      have hu : (⋃ j ∈ insert i F, D j) = D i ∪ ⋃ j ∈ F, D j := by simp
      rw [hu, Finset.sum_insert hi]
      have hD : Disjoint (D i) (⋃ j ∈ F, D j) := by
        apply Set.disjoint_left.mpr
        intro v hvi hvF
        obtain ⟨j, hj, hvj⟩ := Set.mem_iUnion₂.mp hvF
        exact Set.disjoint_left.mp
          (hdis i (by simp) j (by simp [hj]) (by intro he; subst j; exact hi hj)) hvi hvj
      calc
        _ ≤ independence G (D i) + independence G (⋃ j ∈ F, D j) := by
          exact Nat.add_le_add_left (ih
            (fun j hj l hl hne => hdis j (by simp [hj]) l (by simp [hl]) hne)
            (fun j hj l hl hne => hsep j (by simp [hj]) l (by simp [hl]) hne)) _
        _ ≤ _ := independence_add_le Set.subset_union_left Set.subset_union_right hD (by
          intro x hx y hy
          obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
          exact hsep i (by simp) j (by simp [hj])
            (by intro he; subst j; exact hi hj) x hx y hyj)
  exact hh.trans (by simpa only [independence_univ] using
    (independence_mono (G := G) (Set.subset_univ (⋃ i ∈ F, D i))))

 theorem packing_balls {V : Type*} [Fintype V] {G : SimpleGraph V} {X : Set V}
    (F : Finset V) (r w : V → ℕ) (hF : ∀ x ∈ F, x ∈ X)
    (hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ r x + r y + 2 →
      ¬ OutsidePath G X x y d)
    (hweight : ∀ x ∈ F, w x ≤ independence G (outsideBall G X x (r x))) :
    ∑ x ∈ F, w x ≤ G.indepNum := by
  have hh := sum_independence_local G (fun x => outsideBall G X x (r x)) F
    (fun x hx y hy hxy => (outside_balls_separated (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).1)
    (fun x hx y hy hxy => (outside_balls_separated (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).2)
  exact (Finset.sum_le_sum hweight).trans hh

 theorem PathSystem.missing_eq_flat {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing = {x | x ∈ P.singletons.flatten} := by
  classical
  ext x
  constructor
  · intro hx
    exact List.mem_flatten.mpr ⟨[x], by simpa [PathSystem.singletons] using hx, by simp⟩
  · intro hx
    obtain ⟨c, hc, hxc⟩ := List.mem_flatten.mp hx
    have hcf : c ∈ P.chains ∧ c.length = 1 := by simpa [PathSystem.singletons] using hc
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hcf.2
    have he : x = y := by simpa using hxc
    simpa [he] using hcf.1

 theorem PathSystem.missing_subset_reps {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing ⊆ P.representatives := by
  intro x hx
  exact P.rep_of_chain hx (by simp [markedReps])

 theorem PathSystem.missing_ncard {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.missing.ncard = P.singletons.length := by
  classical
  have he : P.missing = (↑P.singletons.flatten.toFinset : Set V) := by
    rw [P.missing_eq_flat]
    ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup, P.singleton_flat_length]
  exact ((List.filter_sublist).flatten).nodup P.nodup

 theorem PathSystem.incident_add_missing {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    P.incident + P.missing.ncard = Q.ncard := by
  rw [P.missing_ncard]
  dsimp [PathSystem.incident]
  exact Nat.sub_add_cancel P.singletons_length_le

 theorem PathSystem.amount_pos_used {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (ha : 0 < P.amount) :
    0 < P.usedChains.length := by
  by_contra! hn
  have he : P.usedChains = [] := List.length_eq_zero_iff.mp (by omega)
  have hh := P.partition.flatten.length_eq
  simp only [he, List.nil_append, P.singleton_flat_length] at hh
  have hle := P.singletons_length_le
  have hf := P.flat_length
  omega

 theorem PathSystem.singleton_extra_rep {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) (ha : 0 < P.amount)
    {x : V} (hx : x ∈ P.missing) :
    ∃ f : List V → Bool, ∃ y : V, y ∈ P.chains.flatten ∧ y ∉ P.reps ∧
      x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps := by
  classical
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil P.usedChains
    (List.length_pos_iff.mp (P.amount_pos_used ha))
  have hcf : c ∈ P.chains ∧ c.length ≠ 1 := by simpa [PathSystem.usedChains] using hc
  apply P.reverse_other_rep hcf.1 hcf.2 (P.missing_subset_reps hx)
  intro hxc
  have hn : c ≠ [x] := by intro he; simp [he] at hcf
  exact List.disjoint_left.mp (P.chains_disjoint hcf.1 hx hn) hxc (by simp)

 theorem PathSystem.interior_representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.representatives \ Q).ncard = P.edgeCount := by
  classical
  have he : P.representatives \ Q =
      (↑(P.reps.filter (fun x => x ∉ Q)).toFinset : Set V) := by ext; simp
  rw [he, Set.ncard_coe_finset, List.toFinset_card_of_nodup
    ((P.reps_sublist.nodup P.nodup).filter _), P.interior_reps_length]

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem two_large_first (h2t : 2 * Q.ncard ≤ k) :
    ∃ x ∈ P.reps, ∃ y ∈ P.reps, x ≠ y ∧
      Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard ∧
      Q.ncard + 1 ≤ (outsideBall G P.vertices y 1).ncard := by
  have ht := H.nine
  by_cases hs : P.vertices.ncard < k
  · have ha : ∀ x ∈ P.reps, Q.ncard + 1 ≤ (outsideBall G P.vertices x 1).ncard := by
      intro x hx
      have hb := outsideBall_degree_bound (P.representatives_subset hx) H.vertices_le
        (show P.representatives \ {x} ⊆ P.vertices from Set.sdiff_subset.trans P.representatives_subset)
        H.degree (H.misses_reps hx)
      rw [Set.ncard_sdiff_singleton_of_mem (show x ∈ P.representatives from hx),
        P.representatives_ncard] at hb
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp (show 1 < P.representatives.ncard by
      rw [P.representatives_ncard]; omega)
    exact ⟨x, hx, y, hy, hxy, ha x hx, ha y hy⟩
  · have hs : P.vertices.ncard = k := by have := H.vertices_le; omega
    have hL : 0 < P.amount := by rw [P.vertices_ncard] at hs; omega
    by_cases he : 2 ≤ P.edgeCount
    · obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp
        (show 1 < (P.representatives \ Q).ncard by rw [P.interior_representatives_ncard]; omega)
      exact ⟨x, hx.1, y, hy.1, hxy, H.interior_degree hx.1 hx.2, H.interior_degree hy.1 hy.2⟩
    · have hmiss : 2 ≤ P.missing.ncard := by
        have hv := P.incident_le_twice_edgeCount
        have hc := P.incident_add_missing
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard).mp (show 1 < P.missing.ncard by omega)
      exact ⟨x, P.missing_subset_reps hx, y, P.missing_subset_reps hy, hxy,
        H.reverse_degree (P.missing_subset_reps hx) (P.singleton_extra_rep hL hx),
        H.reverse_degree (P.missing_subset_reps hy) (P.singleton_extra_rep hL hy)⟩

 
 theorem short : ∃ x ∈ P.reps, ∃ y ∈ P.reps, ∃ d, 2 ≤ d ∧ d ≤ 6 ∧
    OutsidePath G P.vertices x y d := by
  classical
  by_contra hn
  have hno : ∀ x ∈ P.reps, ∀ y ∈ P.reps, ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy d hd hd' hp
    by_cases hd1 : d = 1
    · subst d; exact H.no_one hx hy hp
    · exact hn ⟨x, hx, y, hy, d, by omega, hd', hp⟩
  have hmiss : ∀ x ∈ P.reps, ∀ u ∈ outsideBall G P.vertices x 1,
      ∀ z ∈ P.representatives \ {x}, ¬ G.Adj u z := by
    intro x hx
    apply outsideBall_misses_representatives P.representatives_subset hx
    intro y hy d hd hd'
    exact hno x hx y hy d hd (by omega)
  have hpairs : ∀ x ∈ P.reps, 2 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    exact outsideBall_independent_pair P.representatives_subset hx P.representatives_ncard
      H.vertices_le H.maximal H.degree (hmiss x hx)
  let F := P.reps.toFinset
  have hFc : F.card = Q.ncard := by
    rw [List.toFinset_card_of_nodup (P.reps_sublist.nodup P.nodup), P.reps_length]
  have hpack := packing_balls F (fun _ => 2) (fun _ => 2)
    (fun x hx => P.representatives_subset (List.mem_toFinset.mp hx))
    (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
      (List.mem_toFinset.mp hy) d hd (by omega))
    (fun x hx => hpairs x (List.mem_toFinset.mp hx))
  have h2t : 2 * Q.ncard ≤ k := by
    have hi := H.independent
    simpa only [Finset.sum_const, smul_eq_mul, hFc, Nat.mul_comm] using hpack.trans hi
  obtain ⟨a, ha, b, hb, hab, haB, hbB⟩ := H.two_large_first h2t
  have htriple : ∀ x ∈ P.reps, (x = a ∨ x = b) →
      3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx he
    apply outsideBall_independent_triple (by have := H.nine; omega) (by have := H.nine; omega)
      (by have := H.nine; omega) P.representatives_subset hx P.representatives_ncard
      H.vertices_le H.maximal H.no_cycle H.expansion (hmiss x hx)
    apply H.first_nonclique
    rcases he with rfl | rfl
    · exact haB
    · exact hbB
  let W : V → ℕ := fun x => 2 + if x ∈ ({a,b} : Finset V) then 1 else 0
  have hw : ∀ x ∈ F, W x ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    have hxR := List.mem_toFinset.mp hx
    dsimp [W]
    split_ifs with he
    · exact htriple x hxR (by simpa using he)
    · simpa using hpairs x hxR
  have hpack' := packing_balls F (fun _ => 2) W
    (fun x hx => P.representatives_subset (List.mem_toFinset.mp hx))
    (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
      (List.mem_toFinset.mp hy) d hd (by omega)) hw
  have hsub : ({a,b} : Finset V) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
  have hsum : ∑ x ∈ F, W x = 2 * Q.ncard + 2 := by
    simp only [W, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hFc,
      ← Finset.sum_filter]
    have hfilter : F.filter (fun x => x ∈ ({a,b} : Finset V)) = {a,b} := by
      ext x; simp only [Finset.mem_filter]; exact ⟨And.right, fun hx => ⟨hsub hx, hx⟩⟩
    rw [hfilter]
    simp [hab, Nat.mul_comm]
  rw [hsum] at hpack'
  have hi := hpack'.trans H.independent
  have hk := H.k_le
  omega

end LargeSystem

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem short_information {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) :
    ∃ u v : List V, ∃ D : List (List V), ∃ F : List ℕ,
      P.chains.Perm ((x :: u) :: (y :: v) :: D) ∧
      P.amount = k - Q.ncard ∧ 2 ≤ d ∧
      (D.filter (fun c => c.length = 1)).length + 2 ≤ d ∧
      AmountProfile P F ∧ ∀ a ∈ F, d ≤ a := by
  obtain ⟨I, hIl, hI, hIn, hout⟩ := hp.to_list
  have hI0 : I ≠ [] := by intro he; simp [he] at hIl; omega
  have ho : ∀ z ∈ I, z ∉ Q := fun z hz hq => hout z hz (P.cover z hq)
  simpa only [hIl] using P.short_representatives H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le
    hx hy hp.2.2.1 I hI (positive_interior_chain hI0 ho) hIn
    (List.disjoint_left.mpr hout) hI0 (by omega) ho

 theorem short_heads {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) : x ∈ Q ∧ y ∈ Q := by
  obtain ⟨u, v, D, F, hP, _⟩ := H.short_information hx hy hd hd6 hp
  exact ⟨(P.ends (x :: u) (hP.mem_iff.mpr (by simp))).1 x (by simp),
    (P.ends (y :: v) (hP.mem_iff.mpr (by simp))).1 y (by simp)⟩

 theorem no_short_interior {x y : V} (hx : x ∈ P.reps) (hy : y ∈ P.reps) (hxQ : x ∉ Q)
    (d : ℕ) (hd : 1 ≤ d) (hd6 : d ≤ 6) : ¬ OutsidePath G P.vertices x y d :=
  fun hp => hxQ (H.short_heads hx hy hd hd6 hp).1

 theorem no_short_step {c : List V} (hc : c ∈ P.chains) {x y : V} (A B : List V)
    (he : c = A ++ x :: y :: B) (d : ℕ) (hd : 1 ≤ d) (hd6 : d ≤ 6) :
    ¬ OutsidePath G P.vertices x y d := by
  intro hp
  obtain ⟨I, hIl, hI, hIn, hout⟩ := hp.to_list
  have hI0 : I ≠ [] := by intro hi; simp [hi] at hIl; omega
  have ho : ∀ z ∈ I, z ∉ Q := fun z hz hq => hout z hz (P.cover z hq)
  exact P.not_short_consecutive H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le hc A I B he
    hI (positive_interior_chain hI0 ho) hIn (List.disjoint_left.mpr hout) hI0 (by omega) ho

 theorem parameter {x y : V} {d : ℕ} (hx : x ∈ P.reps) (hy : y ∈ P.reps)
    (hd : 1 ≤ d) (hd6 : d ≤ 6) (hp : OutsidePath G P.vertices x y d) :
    P.amount + Q.ncard = k ∧ (∃ A, AmountProfile P A ∧ ∀ a ∈ A, d ≤ a) ∧
    ((d = 2 ∧ Q.ncard ≤ P.incident + 2 ∧ P.missing ⊆ {x,y}) ∨
     (d = 3 ∧ ((Q.ncard = 9 ∧ P.edgeCount = 3 ∧ P.incident = 6) ∨
                (Q.ncard = 11 ∧ P.edgeCount = 4 ∧ P.incident = 8)) ∧ x ∈ P.missing ∧ y ∈ P.missing) ∨
     (d = 5 ∧ Q.ncard = 9 ∧ k = 19 ∧ P.edgeCount = 2 ∧ P.incident = 4 ∧
       x ∈ P.missing ∧ y ∈ P.missing)) := by
  classical
  obtain ⟨u, v, D, F, hP, hL, hd2, hD, hF, hFd⟩ := H.short_information hx hy hd hd6 hp
  have hsk : P.amount + Q.ncard = k := by have := H.le_k; omega
  have hcount := (hP.filter (fun c => decide (c.length = 1))).length_eq
  change P.singletons.length = _ at hcount
  have huc : ((x :: u).length = 1) ↔ u = [] := by simp
  have hvc : ((y :: v).length = 1) ↔ v = [] := by simp
  simp only [List.filter_cons, huc, hvc] at hcount
  have hsingle : P.singletons.length ≤ (D.filter (fun c => c.length = 1)).length + 2 := by
    split_ifs at hcount <;> (try simp only [List.length_cons] at hcount) <;> omega
  have hvt : Q.ncard ≤ P.incident + d := by
    have hh := P.incident_add_missing
    rw [P.missing_ncard] at hh
    omega
  obtain ⟨hsum, hlen, _⟩ := hF.count
  have hm : d * P.edgeCount ≤ P.amount := by simpa [hsum, hlen] using list_sum_lower F d hFd
  have hc := terminal_classification_numeric H.nine H.k_le hsk P.incident_le_twice_edgeCount hm hvt hd2 hd6
  have hboth : P.singletons.length = d → x ∈ P.missing ∧ y ∈ P.missing := by
    intro hs
    have huv : u = [] ∧ v = [] := by
      split_ifs at hcount with hu hv <;> (try simp only [List.length_cons] at hcount) <;>
        first | exact ⟨of_decide_eq_true hu, of_decide_eq_true hv⟩ | omega
    obtain ⟨rfl, rfl⟩ := huv
    exact ⟨hP.mem_iff.mpr (by simp), hP.mem_iff.mpr (by simp)⟩
  refine ⟨hsk, ⟨F, hF, hFd⟩, ?_⟩
  rcases hc with hc | hc | hc
  · refine Or.inl ⟨hc.1, hc.2, ?_⟩
    have hDz : D.filter (fun c => decide (c.length = 1)) = [] := List.length_eq_zero_iff.mp (by omega)
    intro z hz
    have hz' := hP.mem_iff.mp hz
    simp only [List.mem_cons] at hz'
    rcases hz' with he | he | hz'
    · have hzx : z = x := List.cons.inj he |>.1
      exact Or.inl hzx
    · have hzy : z = y := List.cons.inj he |>.1
      exact Or.inr hzy
    · have hf : [z] ∈ D.filter (fun c => decide (c.length = 1)) := List.mem_filter.mpr ⟨hz', by simp⟩
      simp [hDz] at hf
  · have hs : P.singletons.length = d := by
      have hh := P.incident_add_missing
      rw [P.missing_ncard] at hh
      rcases hc.2 with h9 | h11 <;> omega
    exact Or.inr (Or.inl ⟨hc.1, hc.2, hboth hs⟩)
  · have hs : P.singletons.length = d := by
      have hh := P.incident_add_missing
      rw [P.missing_ncard] at hh
      omega
    exact Or.inr (Or.inr ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hboth hs⟩)

 theorem at_least_two_chains : 2 ≤ P.usedChains.length := by
  obtain ⟨x, hx, y, hy, d, hd, hd6, hp⟩ := H.short
  obtain ⟨hL, ⟨A, hA, hAd⟩, hh⟩ := H.parameter hx hy (by omega) hd6 hp
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A d hAd
  rw [hs, hl] at hm
  have hve := P.incident_eq_edges_add_chains
  have ht := H.nine
  have hk := H.k_le
  rcases hh with ⟨rfl, hv, _⟩ | ⟨rfl, hh, _⟩ | ⟨rfl, ht9, hk19, he, hv, _⟩
  · omega
  · rcases hh with hh | hh <;> omega
  · omega

 theorem second_triple (hk2 : 2 * Q.ncard ≤ k) {x : V} (hx : x ∈ P.reps) :
    3 ≤ independence G (outsideBall G P.vertices x 2) := by
  have hp := H.first_pair (H.two_chains_degree H.at_least_two_chains hx)
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G P.vertices x 1)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := H.expansion I hI hIn
  have hb := outside_neighborhood_bound hIs (Set.empty_subset P.vertices) (by simp)
  simp only [Set.ncard_empty, Nat.add_zero, Nat.reduceAdd] at hb
  have hs := H.vertices_le
  have hm : 2 * k ≤ k * I.ncard := by nlinarith
  apply size_test (by have := H.nine; omega) (by have := H.nine; omega) H.no_cycle H.maximal
  omega

end LargeSystem

 theorem PathSystem.incident_representatives_ncard {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    (P.representatives \ P.missing).ncard = P.incident := by
  have hh := Set.ncard_sdiff_add_ncard_of_subset P.missing_subset_reps
  rw [P.representatives_ncard] at hh
  have hc := P.incident_add_missing
  omega

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem exclude_two_missing (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a)
    (hv : Q.ncard ≤ P.incident + 2) (hM : P.missing.Nonempty) : False := by
  classical
  let J := P.representatives \ P.missing
  have hJc : J.ncard = P.incident := P.incident_representatives_ncard
  have hno : ∀ x ∈ J, ∀ y ∈ J, ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy d hd hd6 hp
    obtain ⟨_, _, hc⟩ := H.parameter hx.1 hy.1 hd hd6 hp
    rcases hc with ⟨_, _, hm⟩ | ⟨_, hh, _⟩ | ⟨_, ht9, _, _, hv4, _⟩
    · obtain ⟨z, hz⟩ := hM
      rcases hm hz with he | he
      · exact hx.2 (he ▸ hz)
      · exact hy.2 (he ▸ hz)
    · rcases hh with hh | hh <;> omega
    · omega
  obtain ⟨A, hA, hAs⟩ := hA
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A 2 hAs
  rw [hs, hl] at hm
  have hve := P.incident_le_twice_edgeCount
  have hk2 : 2 * Q.ncard ≤ k + 2 := by omega
  have hweights : ∀ x ∈ J, 3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    have hpair := H.first_pair (H.two_chains_degree H.at_least_two_chains hx.1)
    obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G P.vertices x 1)
    have he := H.expansion I hI ((Set.ncard_pos).mp (by omega))
    have hmiss : ∀ u ∈ I, ∀ z ∈ J \ {x}, ¬ G.Adj u z := by
      intro u hu z hz
      apply outside_ball_misses (P.representatives_subset hx.1)
        (P.representatives_subset hz.1.1) (Ne.symm hz.2) _ u (hIs hu)
      intro d hd hd'
      exact hno x hx z hz.1 d hd (by omega)
    have hb := outside_neighborhood_bound hIs
      (show J \ {x} ⊆ P.vertices from fun z hz => P.representatives_subset hz.1.1) hmiss
    rw [Set.ncard_sdiff_singleton_of_mem hx, hJc] at hb
    norm_num only at hb
    have hr := H.vertices_le
    have he2 : 2 * k ≤ k * I.ncard := by nlinarith
    apply size_test (by have := H.nine; have := H.le_k; omega)
      (by have := H.nine; omega) H.no_cycle H.maximal
    have ht := H.nine
    change max k (2 * Q.ncard) < (outsideBall G P.vertices x 2).ncard
    omega
  have hp := packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
    (fun x hx => P.representatives_subset (Set.mem_toFinset.mp hx).1)
    (fun x hx y hy _ d hd hd' => hno x (Set.mem_toFinset.mp hx) y
      (Set.mem_toFinset.mp hy) d hd (by omega))
    (fun x hx => hweights x (Set.mem_toFinset.mp hx))
  have hh : 3 * P.incident ≤ k := by
    have ha := hp.trans H.independent
    simpa only [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', hJc, Nat.mul_comm] using ha
  have ht := H.nine
  have hk := H.k_le
  omega

 theorem exclude_three (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 3 ≤ a)
    (hv : (Q.ncard = 9 ∧ P.edgeCount = 3 ∧ P.incident = 6) ∨
      (Q.ncard = 11 ∧ P.edgeCount = 4 ∧ P.incident = 8)) : False := by
  classical
  obtain ⟨A, hA, hAs⟩ := hA
  obtain ⟨hs, hl, _⟩ := hA.count
  have hm := list_sum_lower A 3 hAs
  rw [hs, hl] at hm
  have hk2 : 2 * Q.ncard ≤ k := by rcases hv with hv | hv <;> omega
  have hMc : P.missing.ncard = 3 := by have hh := P.incident_add_missing; rcases hv with hv | hv <;> omega
  obtain ⟨z, hz⟩ := (Set.ncard_pos).mp (show 0 < P.missing.ncard by omega)
  let J := insert z (P.representatives \ P.missing)
  have hJc : J.ncard = P.incident + 1 := by
    rw [Set.ncard_insert_of_notMem (by exact fun h => h.2 hz), P.incident_representatives_ncard]
  have hJR : J ⊆ P.representatives := by
    intro x hx
    rcases hx with rfl | hx
    · exact P.missing_subset_reps hz
    · exact hx.1
  have hJM : ∀ x ∈ J, x ∈ P.missing → x = z := by
    intro x hx hxM
    exact hx.elim id (fun h => (h.2 hxM).elim)
  have hno : ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd6 hp
    obtain ⟨_, _, hc⟩ := H.parameter (hJR hx) (hJR hy) hd hd6 hp
    rcases hc with ⟨_, hv', _⟩ | ⟨_, _, hxM, hyM⟩ | ⟨_, ht9, _, _, hv4, _⟩
    · rcases hv with hv | hv <;> omega
    · exact hxy ((hJM x hx hxM).trans (hJM y hy hyM).symm)
    · rcases hv with hv | hv <;> omega
  have hp := packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
    (fun x hx => P.representatives_subset (hJR (Set.mem_toFinset.mp hx)))
    (fun x hx y hy hxy d hd hd' => hno x (Set.mem_toFinset.mp hx) y
      (Set.mem_toFinset.mp hy) hxy d hd (by omega))
    (fun x hx => H.second_triple hk2 (hJR (Set.mem_toFinset.mp hx)))
  have hh : 3 * (P.incident + 1) ≤ k := by
    simpa only [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', hJc, Nat.mul_comm]
      using hp.trans H.independent
  have hk := H.k_le
  rcases hv with hv | hv <;> omega

 theorem exclude_five (ht : Q.ncard = 9) (hk : k = 19) (hv : P.incident = 4) : False := by
  classical
  let F := P.representatives.toFinset
  let r : V → ℕ := fun x => 1 + if x ∈ P.missing then 0 else 1
  let w : V → ℕ := fun x => 2 + if x ∈ P.missing then 0 else 1
  have hF : ∀ x ∈ F, x ∈ P.reps := by
    intro x hx
    change x ∈ P.representatives
    exact Set.mem_toFinset.mp hx
  have hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ r x + r y + 2 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd' hp
    have hd6 : d ≤ 6 := by dsimp [r] at hd'; split_ifs at hd' <;> omega
    obtain ⟨_, _, hc⟩ := H.parameter (hF x hx) (hF y hy) hd hd6 hp
    rcases hc with ⟨_, hv', _⟩ | ⟨_, hh, _⟩ | ⟨rfl, _, _, _, _, hxM, hyM⟩
    · omega
    · rcases hh with hh | hh <;> omega
    · simp only [r, ite_eq_left hxM, ite_eq_left hyM] at hd'
      omega
  have hw : ∀ x ∈ F, w x ≤ independence G (outsideBall G P.vertices x (r x)) := by
    intro x hx
    by_cases hxM : x ∈ P.missing
    · simpa only [w, r, ite_eq_left hxM, Nat.add_zero] using H.first_pair (H.two_chains_degree H.at_least_two_chains (hF x hx))
    · simpa only [w, r, ite_eq_right hxM, Nat.reduceAdd] using H.second_triple (by omega) (hF x hx)
  have hpack := packing_balls F r w (fun x hx => P.representatives_subset (hF x hx)) hno hw
  have hfilter : F.filter (fun x => x ∉ P.missing) = (P.representatives \ P.missing).toFinset := by
    ext x
    simp [F]
  have hsum : ∑ x ∈ F, w x = 22 := by
    simp only [w, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    have hi : (∑ x ∈ F, if x ∈ P.missing then 0 else 1) =
        (F.filter (fun x => x ∉ P.missing)).card := by
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp_all
    rw [hi, hfilter]
    simp only [F, ← Set.ncard_eq_toFinset_card', P.representatives_ncard,
      P.incident_representatives_ncard, ht, hv]
  rw [hsum] at hpack
  have hi := H.independent
  omega

end LargeSystem

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FiniteGraphs
attribute [-instance] _root_.OAI.CycleClique.globalLabelValid _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph
attribute [local instance] Classical.propDecidable

 theorem chosenChain_sublist {V : Type*} (Q : Set V) (c : List V) :
    (chosenChain Q c).Sublist c := by
  classical
  unfold chosenChain
  split_ifs
  · exact (List.dropLast_sublist _).trans (List.tail_sublist _)
  · exact List.filter_sublist.trans (markedReps_sublist Q true c)

 theorem ClosedChain.four {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hl : c.length = 4) :
    ∃ u a b v, c = [u,a,b,v] ∧ u ∈ Q ∧ v ∈ Q ∧ a ∉ Q ∧ b ∉ Q := by
  rcases c with _ | ⟨u,c⟩ <;> try simp at hl
  rcases c with _ | ⟨a,c⟩ <;> try simp at hl
  rcases c with _ | ⟨b,c⟩ <;> try simp at hl
  rcases c with _ | ⟨v,c⟩ <;> try simp at hl
  have hc : c = [] := List.length_eq_zero_iff.mp (by simpa using hl)
  subst c
  have hu : u ∈ Q := h.ends.1 u (by simp)
  have hv : v ∈ Q := h.ends.2 v (by simp)
  have ha : a ∉ Q := h.positive.rel.resolve_left (not_not.mpr hu)
  have hb : b ∉ Q := h.positive.tail.tail.rel.resolve_right (not_not.mpr hv)
  exact ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩

 theorem ClosedChain.chosen_rep {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) {x : V} (hx : x ∈ chosenChain Q c) :
    x ∉ Q ∧ ∃ b : Bool, x ∈ markedReps Q true (flipChain b c) := by
  classical
  by_cases hl : c.length = 4
  · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := h.four hl
    have hh : x = a ∨ x = b := by simpa [chosenChain] using hx
    rcases hh with rfl | rfl
    · exact ⟨ha, false, by simp [flipChain, markedReps, hu]⟩
    · exact ⟨hb, true, by simp [flipChain, markedReps, hv]⟩
  · have hx' := List.mem_filter.mp (show x ∈ (markedReps Q true c).filter (fun x => x ∉ Q) by
      simpa only [chosenChain, ite_eq_right hl] using hx)
    exact ⟨of_decide_eq_true hx'.2, false, by simpa [flipChain] using hx'.1⟩

 theorem ClosedChain.interior_count {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hn : c.Nodup) {A : List ℕ} (hA : ChainAmounts Q c A) :
    ((markedReps Q true c).filter (fun x => x ∉ Q)).length = A.length := by
  classical
  have hl := markedReps_length Q true c h.nonempty h.ends.2
  have hh := (markedReps Q true c).length_eq_countP_add_countP (fun x => decide (x ∈ Q))
  rw [h.reps_Q_count hn] at hh
  simp only [Bool.not_eq_true, decide_eq_false_iff_not, List.countP_eq_length_filter] at hh
  have hc := hA.count.1
  simp only [ite_true, if_true] at hl
  omega

 theorem ClosedChain.chosen_count {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (h : ClosedChain G Q c) (hn : c.Nodup) {A : List ℕ} (hA : ChainAmounts Q c A)
    (ha : ∀ a ∈ A, 2 ≤ a) (hc1 : c.length ≠ 1) :
    2 * c.countP (fun x => decide (x ∈ Q)) ≤ (chosenChain Q c).length + A.sum := by
  classical
  obtain ⟨hc, hl, _⟩ := hA.count
  have hs := list_sum_lower A 2 ha
  have hAp : 1 ≤ A.length := by
    by_contra! hh
    have he : A = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [he, List.length_nil, List.sum_nil] at hl
    exact hc1 (by omega)
  by_cases h4 : c.length = 4
  · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := h.four h4
    simp only [chosenChain, List.length_cons, List.length_nil, Nat.reduceAdd, ite_true, if_true,
      List.tail_cons, List.dropLast_cons_cons, List.dropLast_singleton]
    simp only [List.length_cons, List.length_nil] at hl
    omega
  · have hi := h.interior_count hn hA
    simp only [chosenChain, ite_eq_right h4, hi]
    by_cases hA1 : A.length = 1
    · have hs3 : 3 ≤ A.sum := by omega
      omega
    · omega

 theorem PathSystem.orient_rep_chain {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (f : List V → Bool) {c : List V} (hc : c ∈ P.chains)
    {x : V} (hx : x ∈ markedReps Q true (flipChain (f c) c)) : x ∈ (P.orient f).reps := by
  apply (P.orient f).rep_of_chain (show flipChain (f c) c ∈ (P.orient f).chains from ?_) hx
  rw [PathSystem.orient_chains]
  exact List.mem_map.mpr ⟨c,hc,rfl⟩

 theorem PathSystem.chosen_rep {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c : List V} (hc : c ∈ P.chains) {x : V}
    (hx : x ∈ chosenChain Q c) : x ∉ Q ∧ ∃ f : List V → Bool, x ∈ (P.orient f).reps := by
  obtain ⟨hxQ,b,hb⟩ := (P.closed_chain hc).chosen_rep hx
  exact ⟨hxQ, fun _ => b, P.orient_rep_chain _ hc hb⟩

 theorem PathSystem.chosen_pair {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) {c c' : List V} (hc : c ∈ P.chains) (hc' : c' ∈ P.chains)
    {x y : V} (hx : x ∈ chosenChain Q c) (hy : y ∈ chosenChain Q c') (hxy : x ≠ y) :
    (∃ f : List V → Bool, x ∈ (P.orient f).reps ∧ y ∈ (P.orient f).reps) ∨
    (∃ u v, c = [u,x,y,v]) ∨ (∃ u v, c = [u,y,x,v]) := by
  classical
  by_cases hcc : c = c'
  · subst c'
    by_cases h4 : c.length = 4
    · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩ := (P.closed_chain hc).four h4
      have hx' : x = a ∨ x = b := by simpa [chosenChain] using hx
      have hy' : y = a ∨ y = b := by simpa [chosenChain] using hy
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact (hxy rfl).elim
      · exact Or.inr (Or.inl ⟨u,v,rfl⟩)
      · exact Or.inr (Or.inr ⟨u,v,rfl⟩)
      · exact (hxy rfl).elim
    · have hx' : x ∈ markedReps Q true c := List.mem_of_mem_filter (by
        simpa only [chosenChain, ite_eq_right h4] using hx)
      have hy' : y ∈ markedReps Q true c := List.mem_of_mem_filter (by
        simpa only [chosenChain, ite_eq_right h4] using hy)
      exact Or.inl ⟨fun _ => false, P.orient_rep_chain _ hc (by simpa [flipChain] using hx'),
        P.orient_rep_chain _ hc (by simpa [flipChain] using hy')⟩
  · obtain ⟨_,b,hb⟩ := (P.closed_chain hc).chosen_rep hx
    obtain ⟨_,b',hb'⟩ := (P.closed_chain hc').chosen_rep hy
    let f : List V → Bool := fun d => if d = c then b else b'
    exact Or.inl ⟨f, P.orient_rep_chain f hc (by simpa [f] using hb),
      P.orient_rep_chain f hc' (by simpa [f, Ne.symm hcc] using hb')⟩

 theorem PathSystem.chosen_sublist {V : Type*} {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) : P.chosen.Sublist P.chains.flatten := by
  suffices hh : ∀ C : List (List V), (C.map (chosenChain Q)).flatten.Sublist C.flatten from hh P.chains
  intro C
  induction C with
  | nil => simp
  | cons c C ih =>
    simpa only [List.map_cons, List.flatten_cons] using (chosenChain_sublist Q c).append ih

 theorem PathSystem.chosen_count {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    (P : PathSystem G Q) (hM : P.missing = ∅)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a) :
    2 * Q.ncard ≤ P.chosen.length + P.amount := by
  classical
  obtain ⟨A, ⟨D,hD,hperm⟩, hAs⟩ := hA
  have hs : D.flatten.sum = P.amount := by
    rw [hperm.sum_eq]
    exact (AmountProfile.count ⟨D,hD,hperm⟩).1
  have hC1 : ∀ c ∈ P.chains, c.length ≠ 1 := by
    intro c hc he
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp he
    have hx : x ∈ P.missing := hc
    rw [hM] at hx
    exact hx
  have hh : ∀ (C : List (List V)) (D : List (List ℕ)), List.Forall₂ (ChainAmounts Q) C D →
      (∀ c ∈ C, c.length ≠ 1) → (∀ a ∈ D.flatten, 2 ≤ a) →
      (∀ c ∈ C, c.Nodup) → (∀ c ∈ C, ClosedChain G Q c) →
      2 * C.flatten.countP (fun x => decide (x ∈ Q)) ≤
      (C.map (chosenChain Q)).flatten.length + D.flatten.sum := by
    intro C D hD
    induction hD with
    | nil => simp
    | @cons c a C D hca hD ih =>
      intro hC1 hdall hnd hc
      have hb := (hc c (by simp)).chosen_count (hnd c (by simp)) hca
        (fun n hn => hdall n (List.mem_flatten.mpr ⟨a,by simp,hn⟩)) (hC1 c (by simp))
      have hi := ih (fun c hc => hC1 c (by simp [hc]))
        (fun n hn => hdall n (List.mem_flatten.mpr (by
          obtain ⟨a,ha,hna⟩ := List.mem_flatten.mp hn
          exact ⟨a,by simp [ha],hna⟩)))
        (fun c hc => hnd c (by simp [hc])) (fun c hc' => hc c (by simp [hc']))
      simp only [List.flatten_cons, List.countP_append, List.map_cons, List.length_append,
        List.sum_append]
      omega
  have hh' := hh P.chains D hD hC1 (fun a ha => hAs a (hperm.mem_iff.mp ha))
    (List.nodup_flatten.mp P.nodup).1 (fun c hc => P.closed_chain hc)
  simpa only [P.clique_count, hs, PathSystem.chosen] using hh'

 theorem OutsidePath.symm {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V} {d : ℕ}
    (h : OutsidePath G X x y d) : OutsidePath G X y x d := by
  obtain ⟨hx,hy,hxy,p,hp,hl,hs⟩ := h
  refine ⟨hy,hx,Ne.symm hxy,p.reverse,hp.reverse,by simpa using hl,?_⟩
  intro v hv hvX
  exact (hs v (by simpa using hv) hvX).symm

namespace LargeSystem
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V} {k : ℕ}
  {P : PathSystem G Q} (H : LargeSystem G Q k P)
include H

 theorem exclude_two_full (hL : P.amount + Q.ncard = k)
    (hA : ∃ A, AmountProfile P A ∧ ∀ a ∈ A, 2 ≤ a) (hM : P.missing = ∅) : False := by
  classical
  have hv : P.incident = Q.ncard := by
    have hh := P.incident_add_missing
    simpa only [hM, Set.ncard_empty, Nat.add_zero] using hh
  have hm : 2 * P.edgeCount ≤ P.amount := by
    obtain ⟨A,hA,ha⟩ := hA
    have hh := list_sum_lower A 2 ha
    simpa only [hA.count.1, hA.count.2.1] using hh
  have hk2 : 2 * Q.ncard ≤ k := by have := P.incident_le_twice_edgeCount; omega
  let F := P.chosen.toFinset
  have hmem : ∀ x ∈ F, ∃ c ∈ P.chains, x ∈ chosenChain Q c := by
    intro x hx
    obtain ⟨l,hl,hx⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hx)
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hl
    exact ⟨c,hc,hx⟩
  have hFX : ∀ x ∈ F, x ∈ P.vertices := by
    intro x hx
    exact P.chosen_sublist.subset (List.mem_toFinset.mp hx)
  have hno : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → ∀ d, 1 ≤ d → d ≤ 6 →
      ¬ OutsidePath G P.vertices x y d := by
    intro x hx y hy hxy d hd hd6 hp
    obtain ⟨c,hc,hxc⟩ := hmem x hx
    obtain ⟨c',hc',hyc⟩ := hmem y hy
    have hxQ := (P.chosen_rep hc hxc).1
    rcases P.chosen_pair hc hc' hxc hyc hxy with ⟨f,hxr,hyr⟩ | ⟨u,v,he⟩ | ⟨u,v,he⟩
    · exact (H.orient f).no_short_interior hxr hyr hxQ d hd hd6 (by simpa using hp)
    · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp
    · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp.symm
  have hw : ∀ x ∈ F, 3 ≤ independence G (outsideBall G P.vertices x 2) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hmem x hx
    obtain ⟨_,f,hxr⟩ := P.chosen_rep hc hxc
    simpa using (H.orient f).second_triple hk2 hxr
  have hpack := packing_balls F (fun _ => 2) (fun _ => 3) hFX
    (fun x hx y hy hxy d hd hd6 => hno x hx y hy hxy d hd (by omega)) hw
  have hc : F.card = P.chosen.length := List.toFinset_card_of_nodup (P.chosen_sublist.nodup P.nodup)
  have hp : 3 * P.chosen.length ≤ k := by
    simpa only [Finset.sum_const, smul_eq_mul, hc, Nat.mul_comm] using hpack.trans H.independent
  have hn := P.chosen_count hM hA
  have ht := H.nine
  have hk := H.k_le
  omega

 theorem contradiction : False := by
  obtain ⟨x,hx,y,hy,d,hd,hd6,hp⟩ := H.short
  obtain ⟨hL,hA,hc⟩ := H.parameter hx hy (by omega) hd6 hp
  rcases hc with ⟨rfl,hv,_⟩ | ⟨rfl,hv,_⟩ | ⟨rfl,ht,hk,he,hv,_⟩
  · by_cases hM : P.missing.Nonempty
    · exact H.exclude_two_missing hL hA hv hM
    · exact H.exclude_two_full hL hA (Set.not_nonempty_iff_eq_empty.mp hM)
  · exact H.exclude_three hL hA hv
  · exact H.exclude_five ht hk hv

end LargeSystem

end CycleClique

namespace CycleClique
open scoped SimpleGraph



namespace FiniteHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ} (H : FiniteHyp G k t)
include H

theorem degree (x : V) : k + 1 ≤ (closedNeighborhood G {x}).ncard := by
  simpa using H.hexp {x} (by intro a ha b hb hab; simp_all) (Set.singleton_nonempty x)

theorem ball_zero_size {X Z : Set V} {x : V} (hx : x ∈ X) (hZ : Z ⊆ X)
    (hxZ : x ∉ Z) (hmiss : ∀ z ∈ Z, ¬ G.Adj x z) :
    k + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x 0).ncard := by
  have hs : closedNeighborhood G {x} ⊆ outsideBall G X x 0 ∪ (X \ Z) := by
    rintro v (hv | ⟨u, hu, huv⟩)
    · have he : v = x := hv
      subst v
      exact Or.inr ⟨hx, hxZ⟩
    · have he : u = x := hu
      subst u
      by_cases hvX : v ∈ X
      · exact Or.inr ⟨hvX, fun hvZ => hmiss v hvZ huv⟩
      · exact Or.inl ⟨huv, hvX⟩
  have hc := Set.ncard_le_ncard hs
  have hu := Set.ncard_union_le (outsideBall G X x 0) (X \ Z)
  have hd := Set.ncard_sdiff_add_ncard_of_subset hZ
  have hh := H.degree x
  omega

theorem ball_zero_pair {X : Set V} {x : V} (hx : x ∈ X)
    (hb : t ≤ (outsideBall G X x 0).ncard) :
    2 ≤ independence G (outsideBall G X x 0) := by
  by_contra hn
  have hC := clique_of_independence_le_one (G := G) (S := outsideBall G X x 0) (by omega)
  have hCx : G.IsClique (insert x (outsideBall G X x 0)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hv.1
    · exact hu.1.symm
    · exact hC hu hv huv
  have hc := (clique_ncard_le_cliqueNum hCx).trans H.hclique
  rw [Set.ncard_insert_of_notMem (show x ∉ outsideBall G X x 0 from
    fun hh => hh.2 hx)] at hc
  omega

theorem ball_step_size {X Z : Set V} {x : V} {r u : ℕ}
    (hu : 1 ≤ u) (hweight : u ≤ independence G (outsideBall G X x r))
    (hZ : Z ⊆ X) (hmiss : ∀ v ∈ outsideBall G X x r, ∀ z ∈ Z, ¬ G.Adj v z) :
    k * u + 1 + Z.ncard ≤ X.ncard + (outsideBall G X x (r + 1)).ncard := by
  obtain ⟨I, hIs, hI, hIc⟩ := exists_indep_of_independence G (outsideBall G X x r)
  have hIn : I.Nonempty := (Set.ncard_pos).mp (by omega)
  have he := H.hexp I hI hIn
  have hb := outside_neighborhood_bound hIs hZ (fun v hv => hmiss v (hIs hv))
  have hm := Nat.mul_le_mul_left k (show u ≤ I.ncard by omega)
  omega

theorem ball_pair {X : Set V} {x : V} {r : ℕ}
    (hb : t < (outsideBall G X x r).ncard) :
    2 ≤ independence G (outsideBall G X x r) := by
  by_contra hn
  have hc := (clique_ncard_le_cliqueNum (clique_of_independence_le_one
    (G := G) (S := outsideBall G X x r) (by omega))).trans H.hclique
  omega

theorem ball_triple {X : Set V} {x : V} {r : ℕ}
    (hb : max k (2 * t) < (outsideBall G X x r).ncard) :
    3 ≤ independence G (outsideBall G X x r) :=
  size_test H.hk (by have := H.ht; omega) H.hcycle H.hclique _ hb

 
theorem ball_stagnation {X Z : Set V} {x : V} {r : ℕ}
    (hx : x ∈ X) (hZ : Z ⊆ X) (hxZ : x ∉ Z)
    (hb : t ≤ (outsideBall G X x r).ncard)
    (hnum : X.ncard + t ≤ k + 1 + Z.ncard)
    (hmiss : ∀ v ∈ outsideBall G X x r, ∀ z ∈ Z, ¬ G.Adj v z) :
    2 ≤ independence G (outsideBall G X x (r + 1)) := by
  by_contra hn
  have hC := clique_of_independence_le_one
    (G := G) (S := outsideBall G X x (r + 1)) (by omega)
  have hc := (clique_ncard_le_cliqueNum hC).trans H.hclique
  have hsub := outsideBall_subset_succ G X x r
  have hadj : ∀ v ∈ outsideBall G X x r, G.Adj x v := by
    intro v hv
    by_contra hneg
    have hZX : insert x Z ⊆ X := Set.insert_subset hx hZ
    have hm : ∀ u ∈ ({v} : Set V), ∀ z ∈ insert x Z, ¬ G.Adj u z := by
      intro u hu z hz huz
      have he : u = v := hu
      subst u
      rcases hz with rfl | hz
      · exact hneg huz.symm
      · exact hmiss v hv z hz huz
    have hh := outside_neighborhood_bound (Set.singleton_subset_iff.mpr hv) hZX hm
    rw [Set.ncard_insert_of_notMem hxZ] at hh
    have hd := H.degree v
    change (closedNeighborhood G {v}).ncard + (Z.ncard + 1) ≤
      X.ncard + (outsideBall G X x (r + 1)).ncard at hh
    omega
  have hbig : G.IsClique (insert x (outsideBall G X x r)) := by
    intro u hu v hv huv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (huv rfl).elim
    · exact hadj v hv
    · exact (hadj u hu).symm
    · exact hC (hsub hu) (hsub hv) huv
  have hbigc := (clique_ncard_le_cliqueNum hbig).trans H.hclique
  rw [Set.ncard_insert_of_notMem (show x ∉ outsideBall G X x r from
    fun hh => outsideBall_subset_compl G X x r hh hx)] at hbigc
  omega

end FiniteHyp


namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

theorem mem_vertices {i : ℕ} (hi : i < n) : S.f i ∈ S.vertices := ⟨i, hi, rfl⟩

theorem card_vertices : S.vertices.ncard = n := by
  rw [vertices, Set.InjOn.ncard_image S.inj, Set.ncard_Iio_nat]

include S in
theorem card_clique : Q.ncard = q.card := by
  rw [S.qimage, Set.InjOn.ncard_image (S.inj.mono S.qb), Set.ncard_coe_finset]

theorem system_amount [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).amount = C.flatten.length - q.card := by
  simp only [PathSystem.amount, S.system_chains, ← List.map_flatten, List.length_map, S.card_clique]

theorem system_edges [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).edgeCount = q.card - C.length := by
  simp only [PathSystem.edgeCount, S.system_chains, List.length_map, S.card_clique]

theorem system_incident [Fintype V] {C : List (List ℕ)} (h : LabelValid n q E C) :
    (S.system h).incident = q.card - (C.filter (fun c => c.length = 1)).length := by
  classical
  simp only [PathSystem.incident, PathSystem.singletons, S.system_chains, List.filter_map,
    Function.comp_def, List.length_map, S.card_clique]

end LabelState

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_BallPacking
attribute [-instance] _root_.OAI.CycleClique.FiniteCertificate.instDecidableValid _root_.OAI.CycleClique.compactLabelCycleValid _root_.OAI.CycleClique.globalLabelAdj _root_.OAI.CycleClique.globalLabelValid _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions _root_.OAI.CycleClique.instDecidablePackingValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem pathLabels_bound {n i j d a : ℕ} (hi : i < n) (hj : j < n)
    (ha : a ∈ pathLabels n i j d) : a < n + d := by
  simp only [pathLabels, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | ha | rfl
  · omega
  · have hh := List.mem_range'.mp ha
    obtain ⟨l, hl, he⟩ := hh
    simp only [Nat.one_mul] at he
    omega
  · omega

namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

theorem extendedFunction_old (I : List V) {i : ℕ} (hi : i < n) :
    S.extendedFunction I i = S.f i := by simp [extendedFunction, hi]

theorem extendedFunction_new (I : List V) {i : ℕ} (hi : i < I.length) :
    S.extendedFunction I (n + i) = I[i] := by
  simp only [extendedFunction, Nat.not_lt.mpr (Nat.le_add_right n i), ite_false, if_false,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem extendedFunction_inj {I : List V} (hI : I.Nodup)
    (hout : ∀ v ∈ I, v ∉ S.vertices) :
    Set.InjOn (S.extendedFunction I) (Set.Iio (n + I.length)) := by
  intro i hi j hj he
  change i < n + I.length at hi
  change j < n + I.length at hj
  by_cases hin : i < n <;> by_cases hjn : j < n
  · rw [S.extendedFunction_old I hin, S.extendedFunction_old I hjn] at he
    exact S.inj hin hjn he
  · have hji : j - n < I.length := by omega
    have hjj : j = n + (j - n) := by omega
    rw [S.extendedFunction_old I hin, hjj, S.extendedFunction_new I hji] at he
    exact (hout _ (List.getElem_mem hji) (he ▸ S.mem_vertices hin)).elim
  · have hii : i - n < I.length := by omega
    have hii' : i = n + (i - n) := by omega
    rw [S.extendedFunction_old I hjn, hii', S.extendedFunction_new I hii] at he
    exact (hout _ (List.getElem_mem hii) (he.symm ▸ S.mem_vertices hjn)).elim
  · have hii : i - n < I.length := by omega
    have hji : j - n < I.length := by omega
    have hii' : i = n + (i - n) := by omega
    have hjj : j = n + (j - n) := by omega
    have hie : S.extendedFunction I i = I[i-n] := by
      calc
        _ = S.extendedFunction I (n + (i-n)) := congrArg _ hii'
        _ = _ := S.extendedFunction_new I hii
    have hje : S.extendedFunction I j = I[j-n] := by
      calc
        _ = S.extendedFunction I (n + (j-n)) := congrArg _ hjj
        _ = _ := S.extendedFunction_new I hji
    have he' : I[i-n] = I[j-n] := hie.symm.trans (he.trans hje)
    have hh := hI.getElem_inj_iff.mp he'
    omega

theorem extendedFunction_range' (I : List V) :
    (List.range' n I.length).map (S.extendedFunction I) = I := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul, S.extendedFunction_new I hi']

theorem exists_extension {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hp : OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ∃ T : LabelState G Q (n + d) q (augmentedEdges n E i j d),
      ∀ a, a < n → T.f a = S.f a := by
  obtain ⟨I, hIl, hchain, hIn, hout⟩ := hp.to_list
  let g := S.extendedFunction I
  have hold : ∀ a, a < n → g a = S.f a := fun a ha => S.extendedFunction_old I ha
  have hmap : (pathLabels n i j d).map g = S.f i :: I ++ [S.f j] := by
    simp only [pathLabels, List.map_cons, List.map_append, List.map_nil, hold i hi, hold j hj,
      ← hIl, g, S.extendedFunction_range', List.cons_append]
  refine ⟨{
    f := g
    inj := by simpa only [← hIl] using S.extendedFunction_inj hIn hout
    qb := fun a ha => by have := S.qb a ha; omega
    qimage := ?_
    eb := ?_
    edges := ?_ }, hold⟩
  · calc
      Q = S.f '' (↑q : Set ℕ) := S.qimage
      _ = g '' (↑q : Set ℕ) := by
        apply Set.image_congr
        intro a ha
        exact (hold a (S.qb a ha)).symm
  · intro a b hab
    rcases List.mem_append.mp hab with hab | hab
    · have hh := S.eb a b hab
      constructor <;> omega
    · have hh := pathEdges_mem hab
      exact ⟨pathLabels_bound hi hj hh.1, pathLabels_bound hi hj hh.2⟩
  · intro a b hab
    rcases hab with hab | hab
    · rcases List.mem_append.mp hab with hab | hab
      · obtain ⟨ha, hb⟩ := S.eb a b hab
        rw [hold a ha, hold b hb]
        exact S.edges a b (Or.inl hab)
      · exact pathEdges_sound g (hmap ▸ hchain) hab
    · rcases List.mem_append.mp hab with hab | hab
      · obtain ⟨hb, ha⟩ := S.eb b a hab
        rw [hold a ha, hold b hb]
        exact S.edges a b (Or.inr hab)
      · exact (pathEdges_sound g (hmap ▸ hchain) hab).symm

end LabelState


theorem cycle_of_list {V : Type*} {G : SimpleGraph V} (L : List V)
    (hl : 3 ≤ L.length) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (he : ∀ x ∈ L.head?, ∀ y ∈ L.getLast?, G.Adj y x) :
    SimpleGraph.cycleGraph L.length ⊑ G := by
  have hne : L ≠ [] := by intro hh; simp [hh] at hl
  let p := SimpleGraph.Walk.ofSupport L hne hc
  have hp : p.IsPath := p.isPath_def.mpr (by simpa [p] using hn)
  have hplen : p.length = L.length - 1 := SimpleGraph.Walk.length_ofSupport _ _
  have hadj := he (L.head hne) (List.head?_eq_some_head hne)
    (L.getLast hne) (List.getLast?_eq_some_getLast hne)
  have hcycle : (SimpleGraph.Walk.cons hadj p).IsCycle := by
    apply (p.cons_isCycle_iff hadj).mpr
    refine ⟨hp, ?_⟩
    intro hh
    have hh' := hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using hh)
    omega
  apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
  refine ⟨_, SimpleGraph.Walk.cons hadj p, hcycle, ?_⟩
  rw [SimpleGraph.Walk.length_cons, hplen]
  omega

theorem LabelState.cycle {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n k : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)
    (hk : 2 ≤ k) {L : List ℕ} (h : LabelCycleValid n k E L) :
    SimpleGraph.cycleGraph (k + 1) ⊑ G := by
  have hc := cycle_of_list (L.map S.f) (by simp only [List.length_map, h.2.1]; omega)
    (h.1.map_on (fun a ha b hb hab => S.inj (h.2.2.1 a ha) (h.2.2.1 b hb) hab))
    ((List.isChain_map S.f).mpr (h.2.2.2.1.imp (fun {a b} hab => S.edges a b hab))) (by
      intro x hx y hy
      simp only [List.head?_map, List.getLast?_map, Option.mem_map] at hx hy
      obtain ⟨a,ha,rfl⟩ := hx
      obtain ⟨b,hb,rfl⟩ := hy
      exact S.edges b a (h.2.2.2.2 a ha b hb))
  have hlen : (L.map S.f).length = k + 1 := by simp only [List.length_map, h.2.1]
  rw [← hlen]
  exact hc



theorem OriginalSystem.impossible {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} {k t L e n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (H : FiniteHyp G k t) (O : OriginalSystem G Q k t L e)
    (S : LabelState G Q n q E) {C : List (List ℕ)}
    (hC : LabelValid n q E C) (hc : Improvement k t L e C) : False := by
  let R := S.system hC
  have hqt : q.card = t := S.card_clique.symm.trans O.card
  have hA : R.amount = C.flatten.length - t := by rw [S.system_amount hC, hqt]
  have he : R.edgeCount = t - C.length := by rw [S.system_edges hC, hqt]
  have hv : R.incident = t - (C.filter (fun c => c.length = 1)).length := by
    rw [S.system_incident hC, hqt]
  change (_ ∧ (_ ∨ (_ ∧ _))) ∨ (_ ∧ _) at hc
  rcases hc with ⟨hsmall, hbetter | ⟨heq,hfewer⟩⟩ | ⟨hl,hu⟩
  · have hh := O.optimal.2.1 R (by rw [O.card, hA]; exact hsmall)
    rw [hA, O.amount] at hh
    omega
  · have hh := O.optimal.2.2 R (by rw [hA, O.amount]; exact heq.symm)
    rw [he, O.edges] at hh
    omega
  · exact R.closing_interval (by have := H.hk; omega) O.clique H.hcycle
      (by rw [O.card]; exact H.htk) (by rw [hA, O.card]; exact hl) (by rw [hA, hv]; exact hu)

 
theorem OutsidePath.restrict {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    {x y : V} {d : ℕ} (h : OutsidePath G Y x y d) (hXY : X ⊆ Y)
    (hx : x ∈ X) (hy : y ∈ X) : OutsidePath G X x y d := by
  obtain ⟨_,_,hne,p,hp,hl,hs⟩ := h
  exact ⟨hx,hy,hne,p,hp,hl,fun v hv hvX => hs v hv (hXY hvX)⟩

theorem LabelState.forbidden_extension {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {n m : ℕ} {q : Finset ℕ} {E F : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) (T : LabelState G Q m q F)
    (hnm : n ≤ m) (he : ∀ i, i < n → T.f i = S.f i)
    {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ¬ OutsidePath G T.vertices (T.f i) (T.f j) d := by
  intro hp
  have hsub : S.vertices ⊆ T.vertices := by
    rintro v ⟨a,ha,rfl⟩
    exact ⟨a, lt_of_lt_of_le ha hnm, he a ha⟩
  rw [he i hi, he j hj] at hp
  exact hno (hp.restrict hsub (S.mem_vertices hi) (S.mem_vertices hj))

namespace ValidMatrix
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} {S : LabelState G Q n q E}
  {M : ForbiddenMatrix} (hM : ValidMatrix S M)
include hM

theorem lookup {i j d : ℕ} (hm : matrixEntry M i j d) :
    ¬ OutsidePath G S.vertices (S.f i) (S.f j) d := by
  rcases hm with hm | hm
  · exact hM.forbidden _ hm
  · intro hp
    exact hM.forbidden _ hm hp.symm

theorem extend {m : ℕ} {F : List (ℕ × ℕ)} (T : LabelState G Q m q F)
    (hnm : n ≤ m) (he : ∀ i, i < n → T.f i = S.f i) : ValidMatrix T M := by
  constructor
  · intro c hc
    exact ⟨lt_of_lt_of_le (hM.bounds c hc).1 hnm, lt_of_lt_of_le (hM.bounds c hc).2 hnm⟩
  · intro c hc
    exact S.forbidden_extension T hnm he (hM.bounds c hc).1 (hM.bounds c hc).2
      (hM.forbidden c hc)

theorem insert {i j d : ℕ} (hi : i < n) (hj : j < n)
    (hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d) :
    ValidMatrix S ((i,j,d) :: M) := by
  constructor
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hi,hj⟩
    · exact hM.bounds c hc
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hno
    · exact hM.forbidden c hc

end ValidMatrix

theorem OutsidePath.of_adj {V : Type*} {G : SimpleGraph V} {X : Set V} {x y : V}
    (hx : x ∈ X) (hy : y ∈ X) (hxy : G.Adj x y) : OutsidePath G X x y 0 := by
  refine ⟨hx, hy, hxy.ne, SimpleGraph.Walk.cons hxy .nil, ?_, rfl, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simpa using hxy.ne
  · intro v hv _
    simpa only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hv


namespace LabelState
variable {V : Type*} {G : SimpleGraph V} {Q : Set V}
  {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (S : LabelState G Q n q E)

theorem imageLabels_card (Z : Finset ℕ) (hZ : ∀ j ∈ Z, j < n) :
    (S.imageLabels Z).ncard = Z.card := by
  rw [imageLabels, Set.InjOn.ncard_image (S.inj.mono hZ), Set.ncard_coe_finset]

theorem imageLabels_subset (Z : Finset ℕ) (hZ : ∀ j ∈ Z, j < n) :
    S.imageLabels Z ⊆ S.vertices := by
  rintro v ⟨j,hj,rfl⟩
  exact S.mem_vertices (hZ j hj)

theorem excluded_notMem {M : ForbiddenMatrix} {i lo hi : ℕ} {Z : Finset ℕ}
    (hib : i < n) (hZ : Excluded n M i lo hi Z) : S.f i ∉ S.imageLabels Z := by
  rintro ⟨j,hj,he⟩
  exact (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hib he)

theorem excluded_zero {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i : ℕ} {Z : Finset ℕ} (hi : i < n) (hZ : Excluded n M i 0 0 Z) :
    ∀ z ∈ S.imageLabels Z, ¬ G.Adj (S.f i) z := by
  rintro z ⟨j,hj,rfl⟩ hij
  exact hM.lookup (hZ.2 j hj 0 (by simp))
    (OutsidePath.of_adj (S.mem_vertices hi) (S.mem_vertices (hZ.1 j hj).1) hij)

theorem excluded_ball {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i r : ℕ} {Z : Finset ℕ} (hi : i < n) (hZ : Excluded n M i 1 (r+1) Z) :
    ∀ v ∈ outsideBall G S.vertices (S.f i) r, ∀ z ∈ S.imageLabels Z, ¬ G.Adj v z := by
  intro v hv z hz
  obtain ⟨j,hj,rfl⟩ := hz
  apply outside_ball_misses (S.mem_vertices hi) (S.mem_vertices (hZ.1 j hj).1)
    (fun he => (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hi he.symm)) _ v hv
  intro d hd hd'
  exact hM.lookup (hZ.2 j hj d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))

end LabelState



namespace BallCertificate

theorem sound {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    {i : ℕ} (hi : i < n) (B : BallCertificate) (h : B.Valid k t n M i) :
    B.size ≤ (outsideBall G S.vertices (S.f i) B.radius).ncard ∧
    1 ≤ B.weight ∧ B.weight ≤ independence G (outsideBall G S.vertices (S.f i) B.radius) := by
  induction B with
  | zero Z b u =>
    rcases h with ⟨hZ,hb,hn,hu,hw⟩
    have hs := H.ball_zero_size (S.mem_vertices hi) (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1))
      (S.excluded_notMem hi hZ) (S.excluded_zero hM hi hZ)
    rw [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] at hs
    have hbound : b ≤ (outsideBall G S.vertices (S.f i) 0).ncard := by omega
    refine ⟨hbound,hu,?_⟩
    rcases hw with hw | ⟨hw,ht⟩
    · exact hw.trans (independence_pos ((Set.ncard_pos).mp (show 0 < (outsideBall G S.vertices (S.f i) 0).ncard by omega)))
    · exact hw.trans (H.ball_zero_pair (S.mem_vertices hi) (ht.trans hbound))
  | succ p Z b u ih =>
    rcases h with ⟨hp,hZ,hb,hu,hw⟩
    obtain ⟨hsize,hpos,hweight⟩ := ih hp
    have hs := H.ball_step_size hpos hweight
      (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1)) (S.excluded_ball hM hi hZ)
    rw [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] at hs
    have hsub := outsideBall_subset_succ G S.vertices (S.f i) p.radius
    have hcard := Set.ncard_le_ncard hsub
    have hbound : b ≤ (outsideBall G S.vertices (S.f i) (p.radius+1)).ncard := by
      rcases hb with hb | hb <;> omega
    refine ⟨hbound,hu,?_⟩
    change u ≤ independence G (outsideBall G S.vertices (S.f i) (p.radius+1))
    rcases hw with hw | ⟨hu2,ht⟩ | ⟨hu3,ht⟩ | ⟨hu2,ht,hn⟩
    · exact hw.trans (hweight.trans (independence_mono hsub))
    · exact hu2.trans (H.ball_pair (ht.trans_le hbound))
    · exact hu3.trans (H.ball_triple (ht.trans_le hbound))
    · apply hu2.trans
      apply H.ball_stagnation (S.mem_vertices hi)
        (S.imageLabels_subset Z (fun j hj => (hZ.1 j hj).1)) (S.excluded_notMem hi hZ)
        (ht.trans hsize) _ (S.excluded_ball hM hi hZ)
      simpa only [S.card_vertices, S.imageLabels_card Z (fun j hj => (hZ.1 j hj).1)] using hn

end BallCertificate

namespace PackingOption

theorem weight_le {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (o : PackingOption) (ho : o.Valid k t n M) :
    o.weight ≤ independence G (o.vertices G S.vertices S.f) := by
  cases o with
  | singleton i => exact independence_pos (Set.singleton_nonempty _)
  | ball i B => exact (B.sound H S hM ho.1 ho.2.2).2.2

theorem separated {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (a b : PackingOption) (ha : a.Valid k t n M) (hb : b.Valid k t n M)
    (hab : a.Compatible M b) :
    Disjoint (a.vertices G S.vertices S.f) (b.vertices G S.vertices S.f) ∧
    ∀ x ∈ a.vertices G S.vertices S.f, ∀ y ∈ b.vertices G S.vertices S.f, ¬ G.Adj x y := by
  have ha' : a.base < n := by cases a with
    | singleton i => exact ha
    | ball i B => exact ha.1
  have hb' : b.base < n := by cases b with
    | singleton i => exact hb
    | ball i B => exact hb.1
  have hne : S.f a.base ≠ S.f b.base := fun he => hab.1 (S.inj ha' hb' he)
  have hm := hab.2
  cases a with
  | singleton i =>
    cases b with
    | singleton j =>
      simp only [radiusCode, Nat.zero_add, base] at hm
      refine ⟨Set.disjoint_singleton.mpr hne, ?_⟩
      rintro x rfl y rfl hij
      exact hM.lookup hm (OutsidePath.of_adj (S.mem_vertices ha') (S.mem_vertices hb') hij)
    | ball j B =>
      simp only [radiusCode, Nat.zero_add, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, base] at hm
      constructor
      · apply Set.disjoint_left.mpr
        rintro x rfl hx
        exact outsideBall_subset_compl G S.vertices (S.f j) B.radius hx (S.mem_vertices ha')
      · rintro x rfl y hy hxy
        apply outside_ball_misses (S.mem_vertices hb') (S.mem_vertices ha') hne.symm _ y hy hxy.symm
        intro d hd hd' hp
        exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩)) hp.symm
  | ball i A =>
    cases b with
    | singleton j =>
      simp only [radiusCode, Nat.add_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, base] at hm
      constructor
      · apply Set.disjoint_left.mpr
        rintro x hx rfl
        exact outsideBall_subset_compl G S.vertices (S.f i) A.radius hx (S.mem_vertices hb')
      · rintro x hx y rfl hxy
        apply outside_ball_misses (S.mem_vertices ha') (S.mem_vertices hb') hne _ x hx hxy
        intro d hd hd'
        exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))
    | ball j B =>
      change (if A.radius+1+(B.radius+1) = 0 then _ else _) at hm
      rw [ite_eq_right (by omega)] at hm
      apply outside_balls_separated (S.mem_vertices ha') (S.mem_vertices hb') hne
      intro d hd hd'
      exact hM.lookup (hm d (Finset.mem_Icc.mpr ⟨hd,by dsimp [radiusCode]; omega⟩))
end PackingOption

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CertificateModel
attribute [-instance] _root_.OAI.CycleClique.globalLabelAdj _root_.OAI.CycleClique.globalLabelValid _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem packing_impossible {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)} (H : FiniteHyp G k t)
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (P : Finset PackingOption) (hP : PackingValid k t n M P) : False := by
  have hs := sum_independence_local G (fun o => o.vertices G S.vertices S.f) P
    (fun a ha b hb hab => (a.separated S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).1)
    (fun a ha b hb hab => (a.separated S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).2)
  have hw : ∑ o ∈ P, o.weight ≤ ∑ o ∈ P, independence G (o.vertices G S.vertices S.f) :=
    Finset.sum_le_sum (fun o ho => o.weight_le H S hM (hP.1 o ho))
  exact (Nat.not_lt_of_ge (hw.trans (hs.trans H.hα))) hP.2.2



namespace FiniteCertificate

theorem sound {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k t L e : ℕ} (H : FiniteHyp G k t) (O : OriginalSystem G Q k t L e)
    (C : FiniteCertificate) {n : ℕ} {q : Finset ℕ} {E : List (ℕ × ℕ)}
    (S : LabelState G Q n q E) {M : ForbiddenMatrix} (hM : ValidMatrix S M)
    (h : C.Valid k t n q E L e M) : False := by
  induction C generalizing n E M with
  | system C => exact O.impossible H S h.1 h.2
  | cycle C => exact H.hcycle (S.cycle (by have := H.hk; omega) h)
  | packing P => exact packing_impossible H S hM P h
  | edge i j =>
    exact hM.lookup h.2.2.2 (OutsidePath.of_adj (S.mem_vertices h.1)
      (S.mem_vertices h.2.1) (S.edges i j h.2.2.1))
  | forbid i j d R N ihR ihN =>
    obtain ⟨hi,hj,hR,hN⟩ := h
    have hno : ¬ OutsidePath G S.vertices (S.f i) (S.f j) d := by
      intro hp
      obtain ⟨T,hT⟩ := S.exists_extension hi hj hp
      exact ihR T (hM.extend T (by omega) hT) hR
    exact ihN S (hM.insert hi hj hno) hN
end FiniteCertificate
open scoped SimpleGraph


theorem normalizedChain_cases (A : List ℕ) : normalizedChain A = A ∨ normalizedChain A = A.reverse :=
  min_choice A A.reverse

theorem normalizedChain_normal (A : List ℕ) : normalizedChain A ≤ (normalizedChain A).reverse := by
  rcases normalizedChain_cases A with h | h
  · rw [h]
    exact h.symm.trans_le (min_le_right A A.reverse)
  · rw [h, List.reverse_reverse]
    exact h.symm.trans_le (min_le_left A A.reverse)

theorem canonicalPattern_sorted (D : List (List ℕ)) : (canonicalPattern D).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : List ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
    (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total a b)
    (D.map normalizedChain)
  simpa only [canonicalPattern, decide_eq_true_eq] using h

theorem canonicalPattern_normal (D : List (List ℕ)) :
    ∀ A ∈ canonicalPattern D, A ≤ A.reverse := by
  intro A hA
  obtain ⟨B,hB,rfl⟩ := List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hA)
  exact normalizedChain_normal B

theorem ClosedChain.reverse {V : Type*} {G : SimpleGraph V} {Q : Set V} {c : List V}
    (hc : ClosedChain G Q c) : ClosedChain G Q c.reverse := by
  refine ⟨by simpa using hc.nonempty, ?_, ?_, ?_⟩
  · exact List.isChain_reverse.mpr (hc.edges.imp (fun _ _ h => h.symm))
  · exact List.isChain_reverse.mpr (hc.positive.imp (fun _ _ h => h.symm))
  · simpa using And.intro hc.ends.2 hc.ends.1

 

theorem normalize_amounts {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {C : List (List V)} {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) C D)
    (hC : ∀ c ∈ C, ClosedChain G Q c) :
    ∃ C', C'.flatten.Perm C.flatten ∧ C'.length = C.length ∧
      List.Forall₂ (ChainAmounts Q) C' (D.map normalizedChain) ∧
      ∀ c ∈ C', ClosedChain G Q c := by
  induction hD with
  | nil => exact ⟨[], List.Perm.refl _, rfl, .nil, by simp⟩
  | @cons c A C D hc hD ih =>
    obtain ⟨C',hp,hl,hD',hC'⟩ := ih (fun d hd => hC d (by simp [hd]))
    rcases normalizedChain_cases A with ha | ha
    · refine ⟨c::C', ?_, by simp [hl], ?_, ?_⟩
      · exact (List.Perm.refl c).append hp
      · simpa only [List.map_cons, ha] using List.Forall₂.cons hc hD'
      · intro d hd
        exact (List.mem_cons.mp hd).elim (fun he => he ▸ hC c (by simp)) (hC' d)
    · refine ⟨c.reverse::C', ?_, by simp [hl], ?_, ?_⟩
      · exact (List.reverse_perm c).append hp
      · simpa only [List.map_cons, ha] using List.Forall₂.cons hc.reverse hD'
      · intro d hd
        exact (List.mem_cons.mp hd).elim (fun he => he ▸ (hC c (by simp)).reverse) (hC' d)

theorem PathSystem.canonical_realization {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q) :
    ∃ (R : PathSystem G Q) (D : List (List ℕ)),
      List.Forall₂ (ChainAmounts Q) R.chains D ∧
      D.Pairwise (· ≤ ·) ∧ (∀ A ∈ D, A ≤ A.reverse) ∧
      R.amount = P.amount ∧ R.edgeCount = P.edgeCount := by
  obtain ⟨A,D,hD,hperm⟩ := P.exists_profile
  obtain ⟨C,hCperm,hClen,hCD,hC⟩ := normalize_amounts hD (fun c hc => P.closed_chain hc)
  have hdperm := List.mergeSort_perm (D.map normalizedChain) (fun a b => decide (a ≤ b))
  obtain ⟨C',hDC',hCperm'⟩ := List.perm_comp_forall₂ hdperm hCD.flip
  have hf : C'.flatten.Perm P.chains.flatten := hCperm'.flatten.trans hCperm
  have hc : ∀ c ∈ C', ClosedChain G Q c := fun c hc => hC c (hCperm'.mem_iff.mp hc)
  let R : PathSystem G Q := {
    chains := C'
    nonempty := fun c hc' => (hc c hc').nonempty
    nodup := hf.nodup_iff.mpr P.nodup
    edges := fun c hc' => (hc c hc').edges
    positive := fun c hc' => (hc c hc').positive
    ends := fun c hc' => (hc c hc').ends
    cover := fun v hv => hf.mem_iff.mpr (P.cover v hv) }
  refine ⟨R, canonicalPattern D, hDC'.flip, canonicalPattern_sorted D,
    canonicalPattern_normal D, ?_, ?_⟩
  · exact congrArg (fun z => z - Q.ncard) hf.length_eq
  · have hl := hCperm'.length_eq.trans hClen
    exact congrArg (fun z => Q.ncard - z) hl

namespace PathSystem

theorem optimal_of_same {V : Type*} [Fintype V] {G : SimpleGraph V} {Q : Set V}
    {k : ℕ} {P R : PathSystem G Q} (hP : P.Optimal k)
    (ha : R.amount = P.amount) (he : R.edgeCount = P.edgeCount) : R.Optimal k := by
  unfold Optimal at hP ⊢
  simpa only [ha,he] using hP

end PathSystem


theorem PathSystem.profile_parameters {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Set V} (P : PathSystem G Q)
    {D : List (List ℕ)} (hD : List.Forall₂ (ChainAmounts Q) P.chains D) :
    patternSize D = Q.ncard ∧ patternAmount D = P.amount ∧
    patternEdgeCount D = P.edgeCount ∧ ∀ a ∈ D.flatten, 0 < a := by
  obtain ⟨ha,he,hpos⟩ := AmountProfile.count (show AmountProfile P D.flatten from ⟨D,hD,List.Perm.refl _⟩)
  have hl := hD.length_eq
  have hle := P.chains_length_le
  refine ⟨?_,ha,he,hpos⟩
  change D.flatten.length+D.length = Q.ncard
  change D.flatten.length = Q.ncard - P.chains.length at he
  omega


theorem mem_chainChoices {A : List ℕ} {l B : ℕ}
    (hl : A.length ≤ l) (hB : A.sum ≤ B) (hpos : ∀ a ∈ A, 0 < a) :
    A ∈ chainChoices l B := by
  induction l generalizing A B with
  | zero =>
    have ha : A = [] := List.length_eq_zero_iff.mp (by omega)
    simp [ha,chainChoices]
  | succ l ih =>
    cases A with
    | nil => simp [chainChoices]
    | cons a A =>
      have ha : 0 < a := hpos a (by simp)
      have hs : a + A.sum ≤ B := by simpa using hB
      simp only [chainChoices, List.mem_cons, List.cons_ne_nil, false_or,
        List.mem_flatMap, List.mem_map]
      refine ⟨a-1, List.mem_range.mpr (by omega), A, ?_, ?_⟩
      · apply ih
        · simpa using hl
        · omega
        · intro b hb; exact hpos b (by simp [hb])
      · congr 1; omega



theorem mem_patternChoices {D : List (List ℕ)} {t B : ℕ} {lower : List ℕ}
    (ht : patternSize D = t) (hB : patternAmount D ≤ B)
    (hpos : ∀ a ∈ D.flatten, 0 < a) (hs : D.Pairwise (· ≤ ·))
    (hn : ∀ A ∈ D, A ≤ A.reverse) (hl : ∀ A ∈ D, lower ≤ A) :
    D ∈ patternChoices t B lower := by
  induction D generalizing t B lower with
  | nil =>
    have ht' : t = 0 := ht.symm
    simp [ht',patternChoices]
  | cons A D ih =>
    have ht' : A.length+1+patternSize D = t := by simpa using ht
    have ht0 : t ≠ 0 := by omega
    have haB : A.sum+patternAmount D ≤ B := by simpa using hB
    have hA : A ∈ chainChoices (t-1) B := mem_chainChoices (by omega) (by omega)
      (fun a ha => hpos a (by simp [ha]))
    rw [patternChoices, dite_eq_right ht0]
    apply List.mem_flatMap.mpr
    refine ⟨A,hA,?_⟩
    rw [ite_eq_left ⟨hn A (by simp),hl A (by simp)⟩]
    apply List.mem_map.mpr
    refine ⟨D,ih ?_ (by omega) (fun a ha => hpos a (by simp [ha]))
      (List.pairwise_cons.mp hs).2 (fun C hC => hn C (by simp [hC]))
      (List.pairwise_cons.mp hs).1, rfl⟩
    omega

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ExteriorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem outsidePath_clique_forbidden {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} (hQ : G.IsClique Q) {k d : ℕ} (hk : 3 ≤ k)
    (ht : Q.ncard ≤ k) (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    {x y : V} (hd : k+1-Q.ncard ≤ d) (hd' : d ≤ k-1) :
    ¬ OutsidePath G Q x y d := by
  classical
  rintro ⟨hx,hy,hxy,p,hp,hlen,hint⟩
  let S := (Q.toFinset.erase x).erase y
  have hs : S.card = Q.ncard-2 := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (by simp [hy,hxy.symm]),
      Finset.card_erase_of_mem (by simpa using hx), ← Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨T,hTS,hTc⟩ := Finset.exists_subset_card_eq (show k-1-d ≤ S.card by omega)
  let C := p.support :: T.toList.map (fun v => [v])
  have hTf : ∀ v ∈ T, v ∈ Q ∧ v ≠ x ∧ v ≠ y := by
    intro v hv
    have hh := hTS hv
    simp only [S,Finset.mem_erase,Set.mem_toFinset] at hh
    exact ⟨hh.2.2,hh.2.1,hh.1⟩
  have hf : C.flatten = p.support ++ T.toList := by simp [C,flatten_singletons]
  have hnd : C.flatten.Nodup := by
    rw [hf,List.nodup_append]
    refine ⟨hp.support_nodup,Finset.nodup_toList _,?_⟩
    intro a ha b hb hab
    subst b
    have hh := hTf a (Finset.mem_toList.mp hb)
    exact (hint a ha hh.1).elim hh.2.1 hh.2.2
  have hc := close_clique_chains hQ C (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · exact p.support_ne_nil
    · simp) hnd (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · exact p.isChain_adj_support
    · simp) (by
    intro c hc
    simp only [C,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨v,hv,rfl⟩
    · constructor
      · intro u hu
        have : u=x := by simpa [List.head?_eq_some_head p.support_ne_nil] using hu.symm
        simpa [this] using hx
      · intro u hu
        have : u=y := by simpa [List.getLast?_eq_some_getLast p.support_ne_nil] using hu.symm
        simpa [this] using hy
    · have hvQ := (hTf v (Finset.mem_toList.mp hv)).1
      simpa using And.intro hvQ hvQ) (by
    rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
    omega)
  have hcL : C.flatten.length = k+1 := by
    rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
    omega
  exact hcycle (hcL ▸ hc)

 
theorem outsidePath_of_list {V : Type*} {G : SimpleGraph V} {Q : Set V}
    {x y : V} {d : ℕ} (L : List V) (hL : L.Nodup) (hchain : L.IsChain G.Adj)
    (hfirst : L.head? = some x) (hlast : L.getLast? = some y)
    (hlen : L.length = d+2) (hx : x ∈ Q) (hy : y ∈ Q)
    (hint : ∀ v ∈ L, v ∈ Q → v=x ∨ v=y) : OutsidePath G Q x y d := by
  have hne : L ≠ [] := by intro he; simp [he] at hfirst
  let p := SimpleGraph.Walk.ofSupport L hne hchain
  have he₁ : L.head hne=x := by simpa only [List.head?_eq_some_head hne,Option.some.injEq] using hfirst
  have he₂ : L.getLast hne=y := by simpa only [List.getLast?_eq_some_getLast hne,Option.some.injEq] using hlast
  let p' := p.copy he₁ he₂
  have hs : p'.support=L := by simp [p',p]
  have hp : p'.IsPath := p'.isPath_def.mpr (hs ▸ hL)
  have hl : p'.length=d+1 := by
    have := p'.length_support
    rw [hs,hlen] at this
    omega
  refine ⟨hx,hy,?_,p',hp,hl,?_⟩
  · intro he
    have := (hp.nil_iff_eq.mpr he).length_eq_zero
    omega
  · simpa only [hs] using hint



theorem extClosed_disjoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q A B : Set V} (hQ : G.IsClique Q) (ht : 3 ≤ Q.ncard) (ht' : Q.ncard ≤ 4)
    (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hA : A ⊆ Qᶜ) (hB : B ⊆ Qᶜ) (hAB : Disjoint A B)
    (hattach : ∀ u ∈ A, ∀ v ∈ B, ∃ x ∈ Q, ∃ y ∈ Q, x ≠ y ∧ G.Adj x u ∧ G.Adj y v) :
    Disjoint (extClosed G Q A) (extClosed G Q B) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  obtain ⟨u,hu,huz⟩ : ∃ u ∈ A, u=z ∨ G.Adj u z := by
    rcases hzA.1 with hu | ⟨u,hu,huz⟩
    · exact ⟨z,hu,Or.inl rfl⟩
    · exact ⟨u,hu,Or.inr huz⟩
  obtain ⟨v,hv,hvz⟩ : ∃ v ∈ B, v=z ∨ G.Adj v z := by
    rcases hzB.1 with hv | ⟨v,hv,hvz⟩
    · exact ⟨z,hv,Or.inl rfl⟩
    · exact ⟨v,hv,Or.inr hvz⟩
  have huv : u ≠ v := fun he => Set.disjoint_left.mp hAB hu (he ▸ hv)
  obtain ⟨x,hx,y,hy,hxy,hxu,hyv⟩ := hattach u hu v hv
  have hun := hA hu
  have hvn := hB hv
  have hz := hzA.2
  have hno2 := outsidePath_clique_forbidden hQ (k:=4) (by omega) ht' hcycle
    (x:=x) (y:=y) (d:=2) (by omega) (by omega)
  have hno3 := outsidePath_clique_forbidden hQ (k:=4) (by omega) ht' hcycle
    (x:=x) (y:=y) (d:=3) (by omega) (by omega)
  have hneq : ∀ w, w ∉ Q → w ≠ x ∧ w ≠ y := by
    intro w hw
    exact ⟨fun he => hw (he ▸ hx),fun he => hw (he ▸ hy)⟩
  have huq := hneq u hun
  have hvq := hneq v hvn
  have hzq := hneq z hz
  have hedge : ¬ G.Adj u v := by
    intro huvAdj
    apply hno2
    apply outsidePath_of_list [x,u,v,y]
    · simp [hxy,huq.2,hvq.2,Ne.symm huq.1,Ne.symm hvq.1,huv]
    · simpa using And.intro hxu (And.intro huvAdj hyv.symm)
    · rfl
    · rfl
    · rfl
    · exact hx
    · exact hy
    · intro w hw hwQ
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hun hwQ).elim
      · exact (hvn hwQ).elim
      · exact Or.inr rfl
  rcases huz with rfl | huz
  · rcases hvz with he | hvz
    · exact huv he.symm
    · exact hedge hvz.symm
  rcases hvz with rfl | hvz
  · exact hedge huz
  apply hno3
  apply outsidePath_of_list [x,u,z,v,y]
  · simp [hxy,huq.2,hvq.2,hzq.2,Ne.symm huq.1,
      Ne.symm hvq.1,Ne.symm hzq.1,huv,huz.ne,hvz.ne.symm]
  · simpa using And.intro hxu (And.intro huz (And.intro hvz.symm hyv.symm))
  · rfl
  · rfl
  · rfl
  · exact hx
  · exact hy
  · intro w hw hwQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (hun hwQ).elim
    · exact (hz hwQ).elim
    · exact (hvn hwQ).elim
    · exact Or.inr rfl


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FrameProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace Frame
variable {V : Type*} {G : SimpleGraph V} {t : ℕ} (T : Frame G t)

theorem memQ (i : Fin t) : T.q i ∈ T.Q := ⟨i,rfl⟩

theorem cardQ [Fintype V] : T.Q.ncard=t := by
  rw [Q,Set.ncard_range_of_injective T.q.injective]
  simp

theorem clique : G.IsClique T.Q := by
  rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ hxy
  exact T.adj i j (fun he => hxy (congrArg T.q he))

theorem exterior (i : Fin t) : T.U i ⊆ T.Qᶜ := fun _ hu => hu.2

theorem neQ {u : V} (hu : u ∉ T.Q) (i : Fin t) : u ≠ T.q i :=
  fun he => hu (he ▸ T.memQ i)

theorem reindex_Q (e : Fin t ≃ Fin t) : (T.reindex e).Q=T.Q := by
  ext u
  constructor
  · rintro ⟨i,rfl⟩
    exact T.memQ _
  · rintro ⟨i,rfl⟩
    exact ⟨e.symm i, by simp [reindex]⟩

theorem reindex_U (e : Fin t ≃ Fin t) (i : Fin t) :
    (T.reindex e).U i=T.U (e i) := by
  simp only [U,reindex_Q]
  rfl


theorem triangle_Q {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (triangle hab hbc hca).Q={a,b,c} := by
  ext u
  simp only [Q,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    change ![a,b,c] i = a ∨ ![a,b,c] i = b ∨ ![a,b,c] i = c
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

end Frame


theorem extClosed_sum_bound {V ι : Type*} [Fintype V] [Fintype ι]
    {G : SimpleGraph V} {Q : Set V} (S : ι → Set V)
    (hdis : Pairwise (fun i j => Disjoint (extClosed G Q (S i)) (extClosed G Q (S j)))) :
    Q.ncard + ∑ i, (extClosed G Q (S i)).ncard ≤ Fintype.card V := by
  classical
  have hc := ncard_union_layers (fun i => extClosed G Q (S i)) hdis Finset.univ
  have hb := Set.ncard_le_ncard (show (⋃ i ∈ Finset.univ,extClosed G Q (S i)) ⊆ Qᶜ from by
    rintro v hv
    obtain ⟨i,_,hi⟩ := Set.mem_iUnion₂.mp hv
    exact hi.2)
  have he := Set.ncard_add_ncard_compl Q
  rw [Nat.card_eq_fintype_card] at he
  omega


theorem extClosed_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    {Q S R : Set V} (hS : S ⊆ Qᶜ) (hne : S.Nonempty)
    (hb : ∀ u ∈ S, ∀ x ∈ Q, G.Adj u x → x ∈ R) :
    k * independence G S + 1 ≤ (extClosed G Q S).ncard + R.ncard := by
  obtain ⟨I,hIS,hI,hIc⟩ := exists_indep_of_independence G S
  have hi := independence_pos (G:=G) hne
  have he := hexp I hI ((Set.ncard_pos).mp (by omega))
  have hs : closedNeighborhood G I ⊆ extClosed G Q S ∪ R := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · right
      rcases hx with hx | ⟨u,hu,hux⟩
      · exact (hS (hIS hx) hxQ).elim
      · exact hb u (hIS hu) x hxQ hux
    · left
      exact ⟨closedNeighborhood_mono G hIS hx,hxQ⟩
  have hc := (Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
  rw [hIc] at he
  omega

theorem extClosed_indep_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    {Q I R : Set V} (hI : G.IsIndepSet I) (hS : I ⊆ Qᶜ) (hne : I.Nonempty)
    (hb : ∀ u ∈ I, ∀ x ∈ Q, G.Adj u x → x ∈ R) :
    k * I.ncard + 1 ≤ (extClosed G Q I).ncard + R.ncard := by
  have hi := indep_ncard_le_independence hI (Set.Subset.refl I)
  exact (by gcongr : k*I.ncard+1 ≤ k*independence G I+1).trans
    (extClosed_expansion hexp hS hne hb)

theorem Frame.U_degree {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ}
    (T : Frame G t) (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k * I.ncard+1 ≤ (closedNeighborhood G I).ncard) (i : Fin t) :
    k+1 ≤ t+(T.U i).ncard := by
  have he := hexp {T.q i} (Set.pairwise_singleton _ _) (Set.singleton_nonempty _)
  have hs : closedNeighborhood G {T.q i} ⊆ T.Q ∪ T.U i := by
    rintro x (rfl | ⟨y,hy,hyx⟩)
    · exact Or.inl (T.memQ i)
    · have he : y=T.q i := hy
      subst y
      by_cases hx : x ∈ T.Q
      · exact Or.inl hx
      · exact Or.inr ⟨hyx,hx⟩
  have hc := (Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
  rw [T.cardQ] at hc
  simp only [Set.ncard_singleton,Nat.mul_one] at he
  omega

theorem Frame.clique_U_bound {V : Type*} [Fintype V] {G : SimpleGraph V} {t u : ℕ}
    (T : Frame G t) (hcl : G.cliqueNum ≤ u) (i : Fin t) (hUi : G.IsClique (T.U i)) :
    (T.U i).ncard+1 ≤ u := by
  have hC : G.IsClique (insert (T.q i) (T.U i)) := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact hy.1
    · exact hx.1.symm
    · exact hUi hx hy hxy
  have hc := (clique_ncard_le_cliqueNum hC).trans hcl
  rwa [Set.ncard_insert_of_notMem (fun hh => hh.2 (T.memQ i))] at hc

theorem Frame.U_ball {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (i : Fin t) : T.U i=outsideBall G T.Q (T.q i) 0 := rfl

theorem Frame.extClosed_U_ball {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (i : Fin t) : extClosed G T.Q (T.U i)=outsideBall G T.Q (T.q i) 1 := by
  ext x
  simp only [extClosed,closedNeighborhood,Set.mem_sdiff,Set.mem_union,Set.mem_ofPred_eq,
    outsideBall,Frame.U,extNeighbors]
  tauto

theorem Frame.boundary_U {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (T : Frame G t) (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
    (i : Fin t) {u x : V} (hu : u ∈ T.U i) (hx : x ∈ T.Q) (hux : G.Adj u x) :
    x ∈ ({T.q i} : Set V) := by
  obtain ⟨j,rfl⟩ := hx
  have hj : j=i := by
    by_contra hji
    exact Set.disjoint_left.mp (hdis hji) (show u ∈ T.U j from ⟨hux.symm,hu.2⟩) hu
  subst j
  rfl

theorem Frame.disjoint_U_expansion {V : Type*} [Fintype V] {G : SimpleGraph V} {k t : ℕ}
    (T : Frame G t) (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
    (i : Fin t) (hne : (T.U i).Nonempty) :
    k * independence G (T.U i) ≤ (extClosed G T.Q (T.U i)).ncard := by
  have hh := extClosed_expansion hexp (T.exterior i) hne (R:={T.q i})
    (fun _ hu _ hx hux => T.boundary_U hdis i hu hx hux)
  simp only [Set.ncard_singleton] at hh
  omega

theorem Frame.disjoint_U_closed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : Frame G 3) (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
    Pairwise (fun i j => Disjoint (extClosed G T.Q (T.U i)) (extClosed G T.Q (T.U j))) := by
  intro i j hij
  apply extClosed_disjoint T.clique (by rw [T.cardQ]) (by rw [T.cardQ]; omega) hcycle
    (T.exterior i) (T.exterior j) (hdis hij)
  intro u hu v hv
  exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,fun he => hij (T.q.injective he),hu.1,hv.1⟩

 

theorem small_four_clique {V : Type*} [Fintype V] {G : SimpleGraph V}
    (horder : Fintype.card V ≤ 17) (hcycle : ¬ SimpleGraph.cycleGraph 5 ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty → 4*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (T : Frame G 4) : False := by
  have hno : ∀ i j : Fin 4, i ≠ j → ∀ d, 1 ≤ d → d ≤ 3 →
      ¬ OutsidePath G T.Q (T.q i) (T.q j) d := by
    intro i j hij d hd hd'
    exact outsidePath_clique_forbidden T.clique (by omega) (by rw [T.cardQ]) hcycle
      (by rw [T.cardQ]; omega) (by omega)
  have hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j)) := by
    intro i j hij
    rw [T.U_ball,T.U_ball]
    exact (outside_balls_separated (T.memQ i) (T.memQ j)
      (fun he => hij (T.q.injective he)) (fun d hd hd' => hno i j hij d hd (by omega))).1
  have hclosed : Pairwise (fun i j => Disjoint (extClosed G T.Q (T.U i))
      (extClosed G T.Q (T.U j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    rw [T.extClosed_U_ball] at hzi hzj
    obtain ⟨d,hd,hd',hp⟩ := outsidePath_of_balls_meet (T.memQ i) (T.memQ j)
      (fun he => hij (T.q.injective he)) hzi hzj
    exact hno i j hij d hd hd' hp
  have hb : ∀ i : Fin 4, 4 ≤ (extClosed G T.Q (T.U i)).ncard := by
    intro i
    have hu := T.U_degree hexp i
    have hne : (T.U i).Nonempty := (Set.ncard_pos).mp (by omega)
    have hi := independence_pos (G:=G) hne
    have he := T.disjoint_U_expansion hexp hdis i hne
    omega
  have hs := extClosed_sum_bound T.U hclosed
  rw [T.cardQ] at hs
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  omega


end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_LowerBound
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem RamseyProperty.on_fintype {m n N : ℕ} (h : RamseyProperty m n N)
    {V : Type*} [Fintype V] (hNV : N ≤ Fintype.card V) (G : SimpleGraph V) :
    SimpleGraph.cycleGraph m ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin N) ≤
    Fintype.card V by simpa using hNV)
  let H := G.comap f
  have hc : H ⊑ G := ⟨⟨⟨f, fun {a b} hab => hab⟩, f.injective⟩⟩
  have hcc : Hᶜ ⊑ Gᶜ := by
    refine ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩
    exact ⟨fun heq => hab.1 (f.injective heq), hab.2⟩
  rcases h H with hcycle | hclique
  · exact Or.inl (hcycle.trans hc)
  · exact Or.inr (hclique.trans hcc)


theorem disjointCliques_walk_fiber {a k : ℕ} {u v : Fin a × Fin k}
    (p : (disjointCliques a k).Walk u v) : u.1 = v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

 
theorem disjointCliques_no_cycle {m a k : ℕ} (hm : 0 < m) (hk : k < m) :
    ¬ SimpleGraph.cycleGraph m ⊑ disjointCliques a k := by
  rintro ⟨f⟩
  let x : Fin m := ⟨0, hm⟩
  have hfiber : ∀ i : Fin m, (f x).1 = (f i).1 := by
    intro i
    obtain ⟨p⟩ := SimpleGraph.cycleGraph_preconnected x i
    exact disjointCliques_walk_fiber (p.map f.toHom)
  have hinj : Function.Injective (fun i : Fin m => (f i).2) := by
    intro i j hij
    apply f.injective
    exact Prod.ext ((hfiber i).symm.trans (hfiber j)) hij
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

 
theorem disjointCliques_no_compl_clique {n a k : ℕ} (ha : a < n) :
    ¬ (⊤ : SimpleGraph (Fin n)) ⊑ (disjointCliques a k)ᶜ := by
  rintro ⟨f⟩
  have hinj : Function.Injective (fun i : Fin n => (f i).1) := by
    intro i j hij
    by_contra hne
    have hadj := f.toHom.map_adj (show (⊤ : SimpleGraph (Fin n)).Adj i j from hne)
    apply hadj.2
    exact ⟨hij, fun heq => hne (f.injective (Prod.ext hij heq))⟩
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

 
theorem ramsey_lower_counterexample {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ¬ RamseyProperty m n ((m - 1) * (n - 1)) := by
  intro h
  have hd := h.on_fintype (G := disjointCliques (n - 1) (m - 1)) (by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact le_of_eq (Nat.mul_comm _ _))
  rcases hd with hc | hk
  · exact disjointCliques_no_cycle (by omega) (by omega) hc
  · exact disjointCliques_no_compl_clique (by omega) hk

 
theorem ramsey_property_lower_bound {m n N : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hN : RamseyProperty m n N) : (m - 1) * (n - 1) + 1 ≤ N := by
  by_contra hnle
  exact ramsey_lower_counterexample hm hn (hN.mono (by omega))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Minimality
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem ramsey_upper_zero (k : ℕ) : RamseyProperty (k + 1) 1 1 := by
  intro G
  right
  refine ⟨⟨⟨id, ?_⟩, Function.injective_id⟩⟩
  intro a b hab
  exact False.elim (hab (Subsingleton.elim a b))

theorem ramsey_upper_one (k : ℕ) : RamseyProperty (k + 1) 2 (k + 1) := by
  classical
  intro G
  by_cases hblue : (⊤ : SimpleGraph (Fin 2)) ⊑ Gᶜ
  · exact Or.inr hblue
  left
  have hi := (no_compl_clique_iff G 1).mp hblue
  have htop : ∀ a b, a ≠ b → G.Adj a b := by
    intro a b hab
    by_contra hn
    have hI : G.IsIndepSet {a, b} := by
      intro x hx y hy hxy hxyadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hn hxyadj
      · exact hn hxyadj.symm
      · exact hxy rfl
    have hc := indep_ncard_le hI
    rw [Set.ncard_pair hab] at hc
    omega
  exact ⟨⟨⟨id, fun {a b} hab => htop a b hab.ne⟩, Function.injective_id⟩⟩

 

theorem order_bound_from_ramsey {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k b : ℕ} (hR : RamseyProperty (k + 1) (b + 1) (k * b + 1))
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hα : G.indepNum ≤ b) :
    Fintype.card V ≤ k * b := by
  by_contra hn
  rcases hR.on_fintype (by omega) G with hc | hb
  · exact hcycle hc
  · exact (no_compl_clique_iff G b).mpr hα hb

 
theorem expansion_of_minimality {k a : ℕ} (G : SimpleGraph (Fin (k * a + 1)))
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hα : G.indepNum ≤ a)
    (hprevious : ∀ b < a, RamseyProperty (k + 1) (b + 1) (k * b + 1))
    {I : Set (Fin (k * a + 1))} (hI : G.IsIndepSet I) (hne : I.Nonempty) :
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard := by
  classical
  have hr : 0 < I.ncard := (Set.ncard_pos).mpr hne
  have hrle : I.ncard ≤ a := (indep_ncard_le hI).trans hα
  let S := (closedNeighborhood G I)ᶜ
  have hprev := hprevious (a - I.ncard) (by omega)
  have hbound := independence_outside_closed hI (Set.subset_univ I)
  rw [independence_univ] at hbound
  have hαS : (G.induce S).indepNum ≤ a - I.ncard := by
    have heq : Set.univ \ closedNeighborhood G I = S := (Set.compl_eq_univ_sdiff _).symm
    rw [heq] at hbound
    change independence G S ≤ a - I.ncard
    omega
  have hcS : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G.induce S := by
    intro hc
    exact hcycle (hc.trans (SimpleGraph.Embedding.induce S).isContained)
  have hc := order_bound_from_ramsey hprev hcS hαS
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hc
  have hsum := Set.ncard_add_ncard_compl (closedNeighborhood G I)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  have hmul : k * (a - I.ncard) + k * I.ncard = k * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hrle]
  change S.ncard ≤ k * (a - I.ncard) at hc
  change (closedNeighborhood G I).ncard + S.ncard = k * a + 1 at hsum
  omega

 

theorem minimal_expanding_counterexample {k a₀ : ℕ} (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k)
    (hfailure : ¬ RamseyProperty (k + 1) (a₀ + 1) (k * a₀ + 1)) :
    ∃ a, 2 ≤ a ∧ a ≤ k ∧ ∃ G : SimpleGraph (Fin (k * a + 1)),
      (¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) ∧ G.indepNum ≤ a ∧
      ∀ I, G.IsIndepSet I → I.Nonempty → k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard := by
  classical
  let A : Set ℕ := {a | 2 ≤ a ∧ a ≤ k ∧
    ¬ RamseyProperty (k + 1) (a + 1) (k * a + 1)}
  have hA : A.Nonempty := ⟨a₀, ha₀, ha₀k, hfailure⟩
  let a := sInf A
  have hamin : a ∈ A := Nat.sInf_mem hA
  obtain ⟨ha, hak, hfail⟩ := hamin
  have hprev : ∀ b < a, RamseyProperty (k + 1) (b + 1) (k * b + 1) := by
    intro b hba
    rcases b with _ | b
    · simpa using ramsey_upper_zero k
    rcases b with _ | b
    · simpa using ramsey_upper_one k
    by_contra hn
    have hbA : b + 2 ∈ A := ⟨by omega, by omega, hn⟩
    have := Nat.sInf_le hbA
    change a ≤ b + 2 at this
    omega
  unfold RamseyProperty at hfail
  obtain ⟨G, hn⟩ := not_forall.mp hfail
  obtain ⟨hcycle, hblue⟩ := not_or.mp hn
  have hα := (no_compl_clique_iff G a).mp hblue
  exact ⟨a, ha, hak, G, hcycle, hα,
    fun I hI hne => expansion_of_minimality G hcycle hα hprev hI hne⟩

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_PatternReduction
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem PatternVerified.impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} {D : List (List ℕ)} (hD : PatternVerified k t D)
    (H : FiniteHyp G k t) (P : PathSystem G Q) (hP : P.Optimal k)
    (hQ : G.IsClique Q) (hc : Q.ncard = t)
    (hprofile : List.Forall₂ (ChainAmounts Q) P.chains D) : False := by
  obtain ⟨C,hC⟩ := hD
  obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero (s := Q) (by have := H.ht; omega)
  obtain ⟨_,ha,he,_⟩ := P.profile_parameters hprofile
  let O : OriginalSystem G Q k t (patternAmount D) (patternEdgeCount D) :=
    ⟨P,hP,hQ,hc,ha.symm,he.symm⟩
  exact C.sound H O (P.labelState hQ hprofile v) (by constructor <;> simp) hC

theorem finite_verified_of_patterns {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} (H : FiniteHyp G k t) (hQ : G.IsClique Q)
    (hc : Q.ncard = t)
    (hverified : ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D) : False := by
  obtain ⟨P,hP⟩ := PathSystem.exists_optimal G Q (k := k) (by have := H.htk; omega)
  obtain ⟨R,D,hD,hs,hn,ha,he⟩ := P.canonical_realization
  have hR := PathSystem.optimal_of_same hP ha he
  obtain ⟨ht,hL,he',hpos⟩ := R.profile_parameters hD
  have hbudget : patternAmount D ≤ k-t := by
    have hp := hR.1
    rw [←hL, hc] at hp
    omega
  have hm := mem_patternChoices (ht.trans hc) hbudget hpos hs hn (lower := []) (fun A _ => le_of_not_gt (by intro h; cases h))
  exact (hverified D hm).impossible H R hR hQ hc hD

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FourCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace FourHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (H : FourHyp G)
include H

theorem U_two (T : Frame G 3) (i : Fin 3) : 2 ≤ (T.U i).ncard := by
  have := T.U_degree H.expansion i
  omega

theorem U_nonempty (T : Frame G 3) (i : Fin 3) : (T.U i).Nonempty :=
  (Set.ncard_pos).mp (lt_of_lt_of_le (by omega : 0<2) (H.U_two T i))

theorem disjoint_triangle (T : Frame G 3)
    (hdis : Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
    ∀ i, (T.U i).ncard=2 ∧ G.IsClique (T.U i) := by
  have hc := T.disjoint_U_closed H.cycle hdis
  have hb := extClosed_sum_bound T.U hc
  rw [T.cardQ,Fin.sum_univ_three] at hb
  have he := fun i => T.disjoint_U_expansion H.expansion hdis i (H.U_nonempty T i)
  have hi := fun i => independence_pos (G:=G) (H.U_nonempty T i)
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  have ho := H.order
  intro i
  have hai : independence G (T.U i) ≤ 1 := by
    fin_cases i <;> dsimp at * <;> omega
  have hcli := clique_of_independence_le_one hai
  have hcu := T.clique_U_bound H.clique i hcli
  have hlo := H.U_two T i
  exact ⟨by omega,hcli⟩

 
theorem exists_overlap (T : Frame G 3) :
    ∃ S : Frame G 3, ∃ i j : Fin 3, i ≠ j ∧ (S.U i ∩ S.U j).Nonempty := by
  classical
  by_contra hn
  have hall : ∀ S : Frame G 3, Pairwise (fun i j => Disjoint (S.U i) (S.U j)) := by
    intro S i j hij
    apply Set.disjoint_left.mpr
    intro u hui huj
    exact hn ⟨S,i,j,hij,u,hui,huj⟩
  have hT := H.disjoint_triangle T (hall T)
  have hsix : ∀ i, 6 ≤ (extClosed G T.Q (T.U i)).ncard := by
    intro i
    obtain ⟨u,v,huv,hUi⟩ := Set.ncard_eq_two.mp (hT i).1
    have hu : u ∈ T.U i := by rw [hUi]; simp
    have hv : v ∈ T.U i := by rw [hUi]; simp
    let W := Frame.triangle hu.1 ((hT i).2 hu hv huv) hv.1.symm
    have hW1 := H.U_two W 1
    have hW2 := H.U_two W 2
    have hdis12 : Disjoint (W.U 1) (W.U 2) := hall W (by decide)
    have hdisU : Disjoint (T.U i) (W.U 1 ∪ W.U 2) := by
      apply Set.disjoint_left.mpr
      intro x hx hxW
      have hxQ : x ∈ W.Q := by
        rw [Frame.triangle_Q]
        rw [hUi] at hx
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
        tauto
      rcases hxW with hxW | hxW <;> exact hxW.2 hxQ
    have hsub : T.U i ∪ (W.U 1 ∪ W.U 2) ⊆ extClosed G T.Q (T.U i) := by
      intro x hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx,hx.2⟩
      have hw : ∃ y ∈ T.U i, G.Adj y x ∧ x ∉ W.Q := by
        rcases hx with hx | hx
        · exact ⟨u,hu,hx.1,hx.2⟩
        · exact ⟨v,hv,hx.1,hx.2⟩
      obtain ⟨y,hy,hyx,hnW⟩ := hw
      refine ⟨Or.inr ⟨y,hy,hyx⟩,?_⟩
      intro hxQ
      have he : x=T.q i := T.boundary_U (hall T) i hy hxQ hyx
      subst x
      exact hnW (W.memQ 0)
    have hb := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdisU,Set.ncard_union_eq hdis12,(hT i).1] at hb
    omega
  have hb := extClosed_sum_bound T.U (T.disjoint_U_closed H.cycle (hall T))
  rw [T.cardQ,Fin.sum_univ_three] at hb
  have h0 := hsix 0
  have h1 := hsix 1
  have h2 := hsix 2
  have ho := H.order
  omega

 
theorem closed_disjoint_of_U (T : Frame G 3) {A B : Set V} {i j : Fin 3}
    (hij : i ≠ j) (hA : A ⊆ T.U i) (hB : B ⊆ T.U j) (hdis : Disjoint A B) :
    Disjoint (extClosed G T.Q A) (extClosed G T.Q B) := by
  apply extClosed_disjoint T.clique (by rw [T.cardQ]) (by rw [T.cardQ]; omega) H.cycle
    (fun _ hu => (hA hu).2) (fun _ hv => (hB hv).2) hdis
  intro u hu v hv
  exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,
    fun he => hij (T.q.injective he),(hA hu).1,(hB hv).1⟩

theorem no_exterior_adj (T : Frame G 3) {u v : V} {i j : Fin 3}
    (hij : i ≠ j) (hu : u ∈ T.U i) (hv : v ∈ T.U j) (huv : u ≠ v) :
    ¬ G.Adj u v := by
  have hd := H.closed_disjoint_of_U T hij (A:={u}) (B:={v})
    (by simpa) (by simpa) (by simp [huv])
  intro he
  exact Set.disjoint_left.mp hd (show v ∈ extClosed G T.Q {u} from
    ⟨Or.inr ⟨u,rfl,he⟩,hv.2⟩) ⟨Or.inl rfl,hv.2⟩

theorem no_triple (T : Frame G 3) {u : V}
    (h0 : u ∈ T.U 0) (h1 : u ∈ T.U 1) : u ∉ T.U 2 := by
  intro h2
  have hc : G.IsClique (insert u T.Q) := by
    have ha : ∀ x ∈ T.Q, G.Adj u x := by
      rintro x ⟨i,rfl⟩
      fin_cases i
      · exact h0.1.symm
      · exact h1.1.symm
      · exact h2.1.symm
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · exact ha y hy
    · exact (ha x hx).symm
    · exact T.clique hx hy hxy
  have hb := (clique_ncard_le_cliqueNum hc).trans H.clique
  rw [Set.ncard_insert_of_notMem h0.2,T.cardQ] at hb
  omega

 
theorem overlap_cycle (T : Frame G 3) {i j l : Fin 3}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {u v : V}
    (hu : u ∈ T.U i ∩ T.U j) (hv : v ∈ T.U i ∩ T.U l) (huv : u ≠ v) : False := by
  have hnu := T.neQ hu.1.2
  have hnv := T.neQ hv.1.2
  apply H.cycle
  apply cycle_of_list [T.q j,u,T.q i,v,T.q l] (by simp)
  · simp [T.q.injective.eq_iff,hil,hjl,Ne.symm hij,hnu,hnv,
      Ne.symm (hnu j),Ne.symm (hnv j),Ne.symm (hnv i),huv]
  · simpa using And.intro hu.2.1 (And.intro hu.1.1.symm
      (And.intro hv.1.1 hv.2.1.symm))
  · simpa using T.adj l j hjl.symm

 
theorem overlap_disjoint_third (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    Disjoint (T.U 0) (T.U 2) ∧ Disjoint (T.U 1) (T.U 2) := by
  obtain ⟨u,hu0,hu1⟩ := hne
  constructor
  · apply Set.disjoint_left.mpr
    intro v hv0 hv2
    have huv : u ≠ v := fun he => H.no_triple T hu0 hu1 (he ▸ hv2)
    exact H.overlap_cycle T (by decide : (0:Fin 3)≠1) (by decide) (by decide)
      ⟨hu0,hu1⟩ ⟨hv0,hv2⟩ huv
  · apply Set.disjoint_left.mpr
    intro v hv1 hv2
    have huv : u ≠ v := fun he => H.no_triple T hu0 hu1 (he ▸ hv2)
    exact H.overlap_cycle T (by decide : (1:Fin 3)≠0) (by decide) (by decide)
      ⟨hu1,hu0⟩ ⟨hv1,hv2⟩ huv

theorem overlap_independent (T : Frame G 3) : G.IsIndepSet (T.U 0 ∩ T.U 1) := by
  intro u hu v hv huv
  exact H.no_exterior_adj T (by decide : (0:Fin 3)≠1) hu.1 hv.2 huv

theorem overlap_closed_pairwise (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    Pairwise (fun i j => Disjoint (extClosed G T.Q (overlapClasses T i))
      (extClosed G T.Q (overlapClasses T j))) := by
  have hd := H.overlap_disjoint_third T hne
  have h01 := H.closed_disjoint_of_U T (by decide : (1:Fin 3)≠0)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 0 \ T.U 1) Set.inter_subset_right Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.2))
  have h02 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠1)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 1 \ T.U 0) Set.inter_subset_left Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.1))
  have h03 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠2)
    (A:=T.U 0 ∩ T.U 1) (B:=T.U 2) Set.inter_subset_left (Set.Subset.refl _)
    (hd.1.mono_left Set.inter_subset_left)
  have h12 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠1)
    (A:=T.U 0 \ T.U 1) (B:=T.U 1 \ T.U 0) Set.sdiff_subset Set.sdiff_subset
    (Set.disjoint_left.mpr (by intro u hu hv; exact hu.2 hv.1))
  have h13 := H.closed_disjoint_of_U T (by decide : (0:Fin 3)≠2)
    (A:=T.U 0 \ T.U 1) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
    (hd.1.mono_left Set.sdiff_subset)
  have h23 := H.closed_disjoint_of_U T (by decide : (1:Fin 3)≠2)
    (A:=T.U 1 \ T.U 0) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
    (hd.2.mono_left Set.sdiff_subset)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [overlapClasses] <;>
    first | exact (hij rfl).elim | assumption | exact h01.symm | exact h02.symm |
      exact h03.symm | exact h12.symm | exact h13.symm | exact h23.symm

 
theorem overlap_structure (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) :
    T.U 0 = T.U 1 ∧ (T.U 0).ncard=2 ∧ G.IsIndepSet (T.U 0) ∧
      (T.U 2).ncard=2 ∧ G.IsClique (T.U 2) := by
  have hd := H.overlap_disjoint_third T hne
  have hI := H.overlap_independent T
  have hbI : ∀ u ∈ T.U 0 ∩ T.U 1, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0,T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · simp
    · simp
    · exact (H.no_triple T hu.1 hu.2 ⟨hux.symm,hu.1.2⟩).elim
  have hbA : ∀ u ∈ T.U 0 \ T.U 1, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · rfl
    · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
    · exact (Set.disjoint_left.mp hd.1 hu.1 ⟨hux.symm,hu.1.2⟩).elim
  have hbB : ∀ u ∈ T.U 1 \ T.U 0, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
    · rfl
    · exact (Set.disjoint_left.mp hd.2 hu.1 ⟨hux.symm,hu.1.2⟩).elim
  have hbD : ∀ u ∈ T.U 2, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 2} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · exact (Set.disjoint_left.mp hd.1 ⟨hux.symm,hu.2⟩ hu).elim
    · exact (Set.disjoint_left.mp hd.2 ⟨hux.symm,hu.2⟩ hu).elim
    · rfl
  have heI := extClosed_indep_expansion H.expansion hI (fun _ hu => hu.1.2) hne hbI
  have hcPair : ({T.q 0,T.q 1} : Set V).ncard=2 := by
    simp [T.q.injective.eq_iff]
  rw [hcPair] at heI
  have heA : (T.U 0 \ T.U 1).Nonempty →
      4 ≤ (extClosed G T.Q (T.U 0 \ T.U 1)).ncard := by
    intro hn
    have hh := extClosed_expansion H.expansion (fun _ hu => hu.1.2) hn hbA
    have hi := independence_pos (G:=G) hn
    simp only [Set.ncard_singleton] at hh
    omega
  have heB : (T.U 1 \ T.U 0).Nonempty →
      4 ≤ (extClosed G T.Q (T.U 1 \ T.U 0)).ncard := by
    intro hn
    have hh := extClosed_expansion H.expansion (fun _ hu => hu.1.2) hn hbB
    have hi := independence_pos (G:=G) hn
    simp only [Set.ncard_singleton] at hh
    omega
  have heD := extClosed_expansion H.expansion (T.exterior 2) (H.U_nonempty T 2) hbD
  simp only [Set.ncard_singleton] at heD
  have hiD := independence_pos (G:=G) (H.U_nonempty T 2)
  have hs := extClosed_sum_bound (overlapClasses T) (H.overlap_closed_pairwise T hne)
  rw [T.cardQ,Fin.sum_univ_four] at hs
  dsimp [overlapClasses] at hs
  have ho := H.order
  have hr := (Set.ncard_pos).mpr hne
  have hU0 := H.U_two T 0
  have hU1 := H.U_two T 1
  have hr2 : (T.U 0 ∩ T.U 1).ncard=2 := by
    have hrne : (T.U 0 ∩ T.U 1).ncard≠1 := by
      intro he
      have hA : (T.U 0 \ T.U 1).Nonempty := by
        by_contra hn
        have hsub : T.U 0 ⊆ T.U 0 ∩ T.U 1 := by
          intro u hu
          refine ⟨hu,?_⟩
          by_contra hh
          exact hn ⟨u,hu,hh⟩
        have := Set.ncard_le_ncard hsub
        omega
      have hB : (T.U 1 \ T.U 0).Nonempty := by
        by_contra hn
        have hsub : T.U 1 ⊆ T.U 0 ∩ T.U 1 := by
          intro u hu
          refine ⟨?_,hu⟩
          by_contra hh
          exact hn ⟨u,hu,hh⟩
        have := Set.ncard_le_ncard hsub
        omega
      have := heA hA
      have := heB hB
      omega
    omega
  have hA0 : (T.U 0 \ T.U 1)=∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    have := heA hn
    omega
  have hB0 : (T.U 1 \ T.U 0)=∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    have := heB hn
    omega
  have hEq : T.U 0=T.U 1 := Set.Subset.antisymm (Set.sdiff_eq_empty.mp hA0)
    (Set.sdiff_eq_empty.mp hB0)
  have hIe : T.U 0 ∩ T.U 1=T.U 0 := by rw [← hEq,Set.inter_self]
  have hDcl := clique_of_independence_le_one (G:=G) (S:=T.U 2) (by omega)
  have hDmax := T.clique_U_bound H.clique 2 hDcl
  have hDmin := H.U_two T 2
  exact ⟨hEq,by simpa only [hIe] using hr2,by simpa only [hIe] using hI,
    by omega,hDcl⟩

 

theorem overlap_vertex_degree (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty)
    {w : V} (hw : w ∈ T.U 0) : (extNeighbors G T.Q w).ncard ≤ 2 := by
  have hs := H.overlap_structure T hne
  have hw1 : w ∈ T.U 1 := hs.1 ▸ hw
  let S := Frame.triangle (T.adj 0 1 (by decide)) hw1.1 hw.1.symm
  have hq2 : T.q 2 ∉ S.Q := by
    rw [Frame.triangle_Q]
    simp [T.q.injective.eq_iff,Ne.symm (T.neQ hw.2 2)]
  have hov : (S.U 0 ∩ S.U 1).Nonempty :=
    ⟨T.q 2,⟨T.adj 0 2 (by decide),hq2⟩,⟨T.adj 1 2 (by decide),hq2⟩⟩
  have hSc := (H.overlap_structure S hov).2.2.2.1
  have hsub : extNeighbors G T.Q w ⊆ S.U 2 := by
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [Frame.triangle_Q]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact hx.2 (T.memQ 0)
    · exact hx.2 (T.memQ 1)
    · exact hx.1.ne rfl
  exact (Set.ncard_le_ncard hsub).trans_eq hSc

 
theorem overlap_contradiction (T : Frame G 3) (hne : (T.U 0 ∩ T.U 1).Nonempty) : False := by
  have hs := H.overlap_structure T hne
  obtain ⟨w,z,hwz,hU⟩ := Set.ncard_eq_two.mp hs.2.1
  have hw : w ∈ T.U 0 := by rw [hU]; simp
  have hz : z ∈ T.U 0 := by rw [hU]; simp
  have hdw := H.overlap_vertex_degree T hne hw
  have hdz := H.overlap_vertex_degree T hne hz
  have hsub : extClosed G T.Q (T.U 0) ⊆
      T.U 0 ∪ (extNeighbors G T.Q w ∪ extNeighbors G T.Q z) := by
    intro x hx
    rcases hx.1 with hxI | ⟨u,hu,hux⟩
    · exact Or.inl hxI
    · rw [hU] at hu
      rcases hu with rfl | rfl
      · exact Or.inr (Or.inl ⟨hux,hx.2⟩)
      · exact Or.inr (Or.inr ⟨hux,hx.2⟩)
  have hb := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
  have hb' := Set.ncard_union_le (extNeighbors G T.Q w) (extNeighbors G T.Q z)
  have hboundary : ∀ u ∈ T.U 0, ∀ x ∈ T.Q, G.Adj u x →
      x ∈ ({T.q 0,T.q 1} : Set V) := by
    rintro u hu x ⟨i,rfl⟩ hux
    fin_cases i
    · simp
    · simp
    · exact (H.no_triple T hu (hs.1 ▸ hu) ⟨hux.symm,hu.2⟩).elim
  have he := extClosed_indep_expansion H.expansion hs.2.2.1 (T.exterior 0)
    (H.U_nonempty T 0) hboundary
  have hc2 : ({T.q 0,T.q 1} : Set V).ncard=2 := by simp [T.q.injective.eq_iff]
  rw [hc2,hs.2.1] at he
  rw [hs.2.1] at hb
  omega

 
theorem contradiction (T : Frame G 3) : False := by
  obtain ⟨S,i,j,hij,hne⟩ := H.exists_overlap T
  let e : Fin 3 ≃ Fin 3 := (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)
  have he0 : e 0=i := by
    fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
  have he1 : e 1=j := by
    fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
  apply H.overlap_contradiction (S.reindex e)
  simpa only [Frame.reindex_U,he0,he1] using hne

end FourHyp

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_ThreeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

namespace ThreeHyp
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {a : ℕ} (H : ThreeHyp G a)
include H

theorem separated (T : Frame G 3) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (T.U i) (T.U j) ∧ ∀ u ∈ T.U i, ∀ v ∈ T.U j, ¬ G.Adj u v := by
  rw [T.U_ball,T.U_ball]
  apply outside_balls_separated (T.memQ i) (T.memQ j) (fun he => hij (T.q.injective he))
  intro d hd hd'
  apply outsidePath_clique_forbidden T.clique (by omega) (by rw [T.cardQ]) H.cycle
  · rw [T.cardQ]
    omega
  · omega

theorem U_nonempty (T : Frame G 3) (i : Fin 3) : (T.U i).Nonempty := by
  have hd := T.U_degree H.expansion i
  exact (Set.ncard_pos).mp (by omega)

theorem alpha_sum (T : Frame G 3) : ∑ i, independence G (T.U i) ≤ a := by
  classical
  have hh := sum_independence_layers G T.U (fun _ _ hij => (H.separated T hij).1)
    Finset.univ (fun _ _ _ _ hij => (H.separated T hij).2)
  have hb := independence_mono (G:=G) (Set.subset_univ (⋃ i ∈ Finset.univ,T.U i))
  rw [independence_univ] at hb
  exact hh.trans (hb.trans H.alpha)

theorem a_eq (T : Frame G 3) : a=3 := by
  have hs := H.alpha_sum T
  rw [Fin.sum_univ_three] at hs
  have h0 := independence_pos (G:=G) (H.U_nonempty T 0)
  have h1 := independence_pos (G:=G) (H.U_nonempty T 1)
  have h2 := independence_pos (G:=G) (H.U_nonempty T 2)
  have := H.a_max
  omega

theorem U_clique (T : Frame G 3) (i : Fin 3) : G.IsClique (T.U i) := by
  have hs := H.alpha_sum T
  rw [Fin.sum_univ_three] at hs
  have h0 := independence_pos (G:=G) (H.U_nonempty T 0)
  have h1 := independence_pos (G:=G) (H.U_nonempty T 1)
  have h2 := independence_pos (G:=G) (H.U_nonempty T 2)
  have := H.a_max
  apply clique_of_independence_le_one
  fin_cases i <;> dsimp at * <;> omega

theorem U_card (T : Frame G 3) (i : Fin 3) : 1 ≤ (T.U i).ncard ∧ (T.U i).ncard ≤ 2 := by
  have hmin := (Set.ncard_pos).mpr (H.U_nonempty T i)
  have hmax := T.clique_U_bound H.clique i (H.U_clique T i)
  omega


omit H in
theorem W_not_U (_H : ThreeHyp G a) (T : Frame G 3) {w : V}
    (hw : w ∈ W T) (i : Fin 3) : w ∉ T.U i :=
  fun hh => hw.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)

theorem W_nonadj_Q (T : Frame G 3) {w : V} (hw : w ∈ W T) (i : Fin 3) : ¬ G.Adj w (T.q i) :=
  fun hh => H.W_not_U T hw i ⟨hh.symm,hw.1⟩

theorem W_card (T : Frame G 3) :
    (W T).ncard + ((T.U 0).ncard + (T.U 1).ncard + (T.U 2).ncard) = 7 := by
  classical
  have hd : Pairwise (fun i j => Disjoint (T.U i) (T.U j)) :=
    fun _ _ hij => (H.separated T hij).1
  have hsum := ncard_union_layers T.U hd Finset.univ
  simp only [Finset.mem_univ,Set.iUnion_true] at hsum
  rw [Fin.sum_univ_three] at hsum
  have hsub : (⋃ i,T.U i) ⊆ T.Qᶜ := by
    intro u hu
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
    exact hi.2
  have he := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hq := Set.ncard_add_ncard_compl T.Q
  rw [T.cardQ,Nat.card_eq_fintype_card,H.order,H.a_eq T] at hq
  change (W T).ncard+(⋃ i,T.U i).ncard = _ at he
  omega

theorem W_nonempty (T : Frame G 3) : (W T).Nonempty := by
  have hw := H.W_card T
  have h0 := H.U_card T 0
  have h1 := H.U_card T 1
  have h2 := H.U_card T 2
  exact (Set.ncard_pos).mp (by omega)

 
theorem W_at_most_one (T : Frame G 3) {w u v : V} (hw : w ∈ W T) {i : Fin 3}
    (hu : u ∈ T.U i) (hv : v ∈ T.U i) (hwu : G.Adj w u) (hwv : G.Adj w v) : u=v := by
  by_contra huv
  have hnw := T.neQ hw.1
  have hnu := T.neQ hu.2
  have hnv := T.neQ hv.2
  apply H.cycle
  apply cycle_of_list [w,u,T.q i,v] (by simp)
  · simp [hwu.ne,hwv.ne,hnw,hnu,Ne.symm (hnv i),huv]
  · simpa using And.intro hwu (And.intro hu.1.symm hv.1)
  · simpa using hwv.symm

 
theorem indep_four_bound {w u v z : V}
    (hwu : w ≠ u) (hwv : w ≠ v) (hwz : w ≠ z)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (nwu : ¬ G.Adj w u) (nwv : ¬ G.Adj w v) (nwz : ¬ G.Adj w z)
    (nuv : ¬ G.Adj u v) (nuz : ¬ G.Adj u z) (nvz : ¬ G.Adj v z) : False := by
  have hI : G.IsIndepSet {w,u,v,z} := by
    intro x hx y hy hxy hadj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | exact hxy rfl | exact nwu hadj | exact nwu hadj.symm |
        exact nwv hadj | exact nwv hadj.symm | exact nwz hadj | exact nwz hadj.symm |
        exact nuv hadj | exact nuv hadj.symm | exact nuz hadj | exact nuz hadj.symm |
        exact nvz hadj | exact nvz hadj.symm
  have hc : ({w,u,v,z} : Set V).ncard=4 := by
    simp [Set.ncard_insert_of_notMem,hwu,hwv,hwz,huv,huz,hvz]
  have hb := (indep_ncard_le hI).trans H.alpha
  have := H.a_max
  omega

 
theorem W_no_two_misses (T : Frame G 3) {w u v : V} (hw : w ∈ W T)
    {i j : Fin 3} (hij : i ≠ j) (hu : u ∈ T.U i) (hv : v ∈ T.U j)
    (hwu : ¬ G.Adj w u) (hwv : ¬ G.Adj w v) : False := by
  obtain ⟨l,hli,hlj⟩ : ∃ l : Fin 3, l ≠ i ∧ l ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  have hdis := (H.separated T hij).1
  have hnu := T.neQ hu.2
  have hnv := T.neQ hv.2
  apply H.indep_four_bound (w:=w) (u:=u) (v:=v) (z:=T.q l) (fun he => H.W_not_U T hw i (he ▸ hu))
    (fun he => H.W_not_U T hw j (he ▸ hv)) (T.neQ hw.1 l)
    (fun he => Set.disjoint_left.mp hdis hu (he ▸ hv)) (hnu l) (hnv l)
    hwu hwv (H.W_nonadj_Q T hw l) ((H.separated T hij).2 u hu v hv)
  · intro hh
    exact Set.disjoint_left.mp (H.separated T hli).1 ⟨hh.symm,hu.2⟩ hu
  · intro hh
    exact Set.disjoint_left.mp (H.separated T hlj).1 ⟨hh.symm,hv.2⟩ hv

 
theorem W_two_complete (T : Frame G 3) {w : V} (hw : w ∈ W T) :
    ∃ h : Fin 3, ∀ i, i ≠ h → ∀ u ∈ T.U i, G.Adj w u := by
  classical
  by_cases hbad : ∃ i : Fin 3, ¬ ∀ u ∈ T.U i, G.Adj w u
  · obtain ⟨h,hh⟩ := hbad
    push Not at hh
    obtain ⟨v,hv,hwv⟩ := hh
    refine ⟨h,?_⟩
    intro i hih u hu
    by_contra hwu
    exact H.W_no_two_misses T hw hih hu hv hwu hwv
  · push Not at hbad
    exact ⟨0,fun i _ => hbad i⟩

theorem W_complete_singleton (T : Frame G 3) {w : V} (hw : w ∈ W T) (i : Fin 3)
    (hi : ∀ u ∈ T.U i, G.Adj w u) : (T.U i).ncard=1 := by
  obtain ⟨u,hu⟩ := H.U_nonempty T i
  have he : T.U i={u} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hu,?_⟩
    intro v hv
    exact H.W_at_most_one T hw hv hu (hi v hv) (hi u hu)
  simp [he]

theorem W_at_least_three (T : Frame G 3) : 3 ≤ (W T).ncard := by
  obtain ⟨w,hw⟩ := H.W_nonempty T
  obtain ⟨h,hh⟩ := H.W_two_complete T hw
  have hs := H.W_card T
  have hmax := (H.U_card T h).2
  have hc : ∀ i, i ≠ h → (T.U i).ncard=1 := by
    intro i hi
    exact H.W_complete_singleton T hw i (hh i hi)
  fin_cases h
  · have h1 := hc 1 (by decide)
    have h2 := hc 2 (by decide)
    dsimp at *
    omega
  · have h0 := hc 0 (by decide)
    have h2 := hc 2 (by decide)
    dsimp at *
    omega
  · have h0 := hc 0 (by decide)
    have h1 := hc 1 (by decide)
    dsimp at *
    omega

 
theorem no_two_common {x y u v : V} (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) (hyu : G.Adj y u) (hyv : G.Adj y v) : False := by
  apply H.cycle
  apply cycle_of_list [x,u,y,v] (by simp)
  · simp [hxu.ne,hxv.ne,hyu.ne.symm,hyv.ne,hxy,huv]
  · simpa using And.intro hxu (And.intro hyu.symm hyv)
  · simpa using hxv.symm

 

theorem contradiction (T : Frame G 3) : False := by
  classical
  let f : W T → Fin 3 := fun w => (H.W_two_complete T w.property).choose
  have hf : ∀ w : W T, ∀ i, i ≠ f w → ∀ u ∈ T.U i, G.Adj w.val u :=
    fun w => (H.W_two_complete T w.property).choose_spec
  have hinj : Function.Injective f := by
    intro w w' he
    apply Subtype.ext
    by_contra hww
    obtain ⟨i,j,hij,hi,hj⟩ : ∃ i j : Fin 3, i ≠ j ∧ i ≠ f w ∧ j ≠ f w := by
      generalize f w = l
      fin_cases l <;> decide
    obtain ⟨u,hu⟩ := H.U_nonempty T i
    obtain ⟨v,hv⟩ := H.U_nonempty T j
    have huv : u ≠ v := fun he => Set.disjoint_left.mp (H.separated T hij).1 hu (he ▸ hv)
    exact H.no_two_common hww huv (hf w i hi u hu) (hf w j hj v hv)
      (hf w' i (he ▸ hi) u hu) (hf w' j (he ▸ hj) v hv)
  have hcW : Fintype.card (W T)=(W T).ncard := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hupper : (W T).ncard ≤ 3 := by
    have hh := Fintype.card_le_of_injective f hinj
    simpa only [hcW,Fintype.card_fin] using hh
  have hlower := H.W_at_least_three T
  have hvar : ∀ i : Fin 3, ∃ w : W T, f w ≠ i := by
    intro i
    by_contra hh
    push Not at hh
    have hsub : Subsingleton (W T) := ⟨fun w w' => hinj ((hh w).trans (hh w').symm)⟩
    have hhcard := Fintype.card_le_one_iff_subsingleton.mpr hsub
    rw [hcW] at hhcard
    omega
  have hone : ∀ i, (T.U i).ncard=1 := by
    intro i
    obtain ⟨w,hw⟩ := hvar i
    exact H.W_complete_singleton T w.property i (hf w i hw.symm)
  have h0 := hone 0
  have h1 := hone 1
  have h2 := hone 2
  have hc := H.W_card T
  omega

end ThreeHyp

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_StructuralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem Frame.exists_of_cliqueNum {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (ht : t ≤ G.cliqueNum) : Nonempty (Frame G t) := by
  obtain ⟨f⟩ := (complete_isContained_iff_le_cliqueNum G t).mpr ht
  exact ⟨⟨f.toEmbedding, fun i j hij => f.toHom.map_rel' (by simpa using hij)⟩⟩

 
theorem reduced_small_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (hk' : k ≤ 4) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  have hthree : 3 ≤ G.cliqueNum := (le_max_left _ _).trans hl
  obtain ⟨T⟩ := Frame.exists_of_cliqueNum hthree
  interval_cases k
  · exact (show ThreeHyp G a from ⟨horder,hα,hak,hcycle,hu,hexp⟩).contradiction T
  · have ho : Fintype.card V ≤ 17 := by omega
    by_cases hfour : 4 ≤ G.cliqueNum
    · obtain ⟨S⟩ := Frame.exists_of_cliqueNum hfour
      exact small_four_clique ho hcycle hexp S
    · exact (show FourHyp G from ⟨ho,hcycle,by omega,hexp⟩).contradiction T

 

theorem reduced_large_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard)
    (hnine : 9 ≤ G.cliqueNum) : False := by
  classical
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  obtain ⟨Q,hQ⟩ := G.exists_isNClique_cliqueNum
  have hc : (Q : Set V).ncard = G.cliqueNum := by
    rw [Set.ncard_coe_finset,hQ.card_eq]
  obtain ⟨P,hP⟩ := PathSystem.exists_optimal G (Q : Set V) (k:=k) (by omega)
  have hhalf : k/2 ≤ G.cliqueNum := (le_max_right _ _).trans hl
  have H : LargeSystem G (Q : Set V) k P :=
    ⟨hP,hQ.isClique,hcycle,by omega,by omega,by omega,by omega,hα.trans hak,hexp⟩
  exact H.contradiction

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FiniteRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph



theorem finite_verification {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k t : ℕ} (hk : 5 ≤ k) (_ : k ≤ 17)
    (hl : max 3 (k/2) ≤ t) (hu : t ≤ min 8 k)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G) (hclique : G.cliqueNum = t)
    (hα : G.indepNum ≤ k)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  classical
  obtain ⟨Q,hQ⟩ := G.exists_isNClique_cliqueNum
  have hc : (Q : Set V).ncard = t := by
    rw [Set.ncard_coe_finset,hQ.card_eq,hclique]
  have ht : 3 ≤ t := (le_max_left _ _).trans hl
  have ht8 : t ≤ 8 := hu.trans (min_le_left _ _)
  have htk : t ≤ k := hu.trans (min_le_right _ _)
  have hhalf : k/2 ≤ t := (le_max_right _ _).trans hl
  have H : FiniteHyp G k t := ⟨hk,ht,htk,hcycle,le_of_eq hclique,hα,hexp⟩
  exact finite_verified_of_patterns H hQ.isClique hc
    (finite_range_verified hk ht htk ht8 hhalf)

 

theorem reduced_counterexample_impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (horder : Fintype.card V = k*a+1) (hα : G.indepNum ≤ a)
    (hcycle : ¬ SimpleGraph.cycleGraph (k+1) ⊑ G)
    (hexp : ∀ I, G.IsIndepSet I → I.Nonempty →
      k*I.ncard+1 ≤ (closedNeighborhood G I).ncard) : False := by
  classical
  by_cases hsmall : k ≤ 4
  · exact reduced_small_impossible hk hsmall ha hak horder hα hcycle hexp
  by_cases hnine : 9 ≤ G.cliqueNum
  · exact reduced_large_impossible hk ha hak horder hα hcycle hexp hnine
  obtain ⟨hl,hu⟩ := counterexample_clique_bound hk ha hak horder hα hcycle hexp
  exact finite_verification (by omega) (by omega) hl (by omega) hcycle rfl
    (hα.trans hak) hexp

 
theorem ramsey_upper {k a₀ : ℕ} (hk : 3 ≤ k) (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k) :
    RamseyProperty (k+1) (a₀+1) (k*a₀+1) := by
  by_contra hfailure
  obtain ⟨a,ha,hak,G,hcycle,hα,hexp⟩ := minimal_expanding_counterexample ha₀ ha₀k hfailure
  exact reduced_counterexample_impossible hk ha hak (Fintype.card_fin _) hα hcycle hexp

 

theorem main (m n : ℕ) (hmn : n ≤ m) (hn : 3 ≤ n)
    (hne : (m, n) ≠ (3, 3)) :
    cycleCliqueRamsey m n = (m - 1) * (n - 1) + 1 := by
  have hm : 4 ≤ m := by
    by_contra hh
    have hm3 : m=3 := by omega
    have hn3 : n=3 := by omega
    exact hne (by simp [hm3,hn3])
  have hupper : RamseyProperty m n ((m-1)*(n-1)+1) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega),
      Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (ramsey_upper (k:=m-1) (a₀:=n-1) (by omega) (by omega) (by omega))
  apply le_antisymm
  · exact Nat.sInf_le hupper
  · have hmem : RamseyProperty m n (cycleCliqueRamsey m n) :=
      Nat.sInf_mem (s:={N | RamseyProperty m n N}) ⟨(m-1)*(n-1)+1,hupper⟩
    exact ramsey_property_lower_bound (by omega) (by omega) hmem

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_MainTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem thm_main_oai :
    (∀ m n : ℤ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
      (cycleCliqueRamsey m.toNat n.toNat : ℤ) = (m - 1) * (n - 1) + 1) ∧
    cycleCliqueRamsey 3 3 = 6 := by
  constructor
  · intro m n hmn hn hne
    have hmnN : n.toNat ≤ m.toNat := by omega
    have hnN : 3 ≤ n.toNat := by omega
    have hneN : (m.toNat, n.toNat) ≠ (3, 3) := by
      intro he
      have hm3 := congrArg Prod.fst he
      have hn3 := congrArg Prod.snd he
      have hm3' : m = 3 := by omega
      have hn3' : n = 3 := by omega
      exact hne (by simp [hm3', hn3'])
    have h := main m.toNat n.toNat hmnN hnN hneN
    have hmcast : ((m.toNat - 1 : ℕ) : ℤ) = m - 1 := by omega
    have hncast : ((n.toNat - 1 : ℕ) : ℤ) = n - 1 := by omega
    have hcast := congrArg (fun a : ℕ => (a : ℤ)) h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hmcast, hncast] using hcast
  · exact exceptional

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.thm_main_oai := @OAI.CycleClique.thm_main_oai
