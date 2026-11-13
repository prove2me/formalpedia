-- Prove2me | solution 1 for MultipleUnicast.Counterexample.restriction_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:49:18.759693+00:00
-- url     : https://prove2.me/submissions/13a116a8-a132-4124-93a0-b7324b792a38

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph
import Definitions.Def_MultipleUnicast_Counterexample_Protocol
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation
import Theorems.Thm_MultipleUnicast_Counterexample_dimension_bound

section
set_option maxRecDepth 4096
set_option autoImplicit false
namespace MultipleUnicast.Counterexample.Dev.Bal
open MultipleUnicast.Counterexample


end MultipleUnicast.Counterexample.Dev.Bal
end

section
set_option maxRecDepth 4096
set_option autoImplicit false

namespace MultipleUnicast.Counterexample.Dev.TermDist
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Bal Matrix

/-! ### Spanning-tree certificate: `parL v` is a physical edge joining `v` to `upL v`,
and `depL (upL v) < depL v`. -/

/-! ### Bipartiteness -/

theorem pe_lt (q : Edge) : (pointEnd q).val < 91 := (edgePair q).1.isLt
theorem le_ge (q : Edge) : 91 ≤ (lineEnd q).val := Nat.le_add_right _ _

/-! ### Every candidate edge is an incidence -/

theorem inc (q : Edge) : dot (triple (edgePair q).1) (triple (edgePair q).2) = 0 := by
  have hl := balanced_orientation.1
  have hlt : q.val < incidenceList.length := by omega
  have hm : edgePair q ∈ incidenceList := by
    unfold edgePair
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem _
  unfold incidenceList at hm
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hm
  obtain ⟨i, j, hj, hij⟩ := hm
  rw [← hij]
  exact hj

/-! ### Two distinct points lie on at most one common line -/

def Nrm (u : Triple) : Prop := (u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 1) ∨ (u 0 = 0 ∧ u 1 = 1) ∨ u 0 = 1

theorem nrm_triple (i : Fin 91) : Nrm (triple i) := by
  unfold triple Nrm
  split_ifs <;> simp

theorem cross_zero_eq {u v : Triple} (hu : Nrm u) (hv : Nrm v) (h : u ⨯₃ v = 0) : u = v := by
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := congrFun h 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := congrFun h 1
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := congrFun h 2
  clear h
  have e : u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = v 2 := by
    rcases hu with ⟨a0, a1, a2⟩ | ⟨a0, a1⟩ | a0 <;>
    rcases hv with ⟨b0, b1, b2⟩ | ⟨b0, b1⟩ | b0 <;> grind
  funext k
  fin_cases k
  exacts [e.1, e.2.1, e.2.2]

def code (c : F9) : ℕ := c.re.val + 3 * c.im.val

def dec (u : Triple) : ℕ :=
  if code (u 0) = 0 then (if code (u 1) = 0 then 0 else 1 + code (u 2))
  else 10 + 9 * code (u 1) + code (u 2)

theorem dec_triple : ∀ i : Fin 91, dec (triple i) = i.val := by decide +kernel

theorem triple_inj : Function.Injective triple := fun i j h =>
  Fin.ext (by rw [← dec_triple i, ← dec_triple j, h])

/-! ### No short walks between the ends of a deleted edge -/

end MultipleUnicast.Counterexample.Dev.TermDist

namespace MultipleUnicast.Counterexample


end MultipleUnicast.Counterexample
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false

/-! Local part of `restriction_isomorphism`: the five known positions at a vertex determine
the five local coefficients, and local interpolation is a linear left inverse. -/

namespace MultipleUnicast.Counterexample.Dev.RILocal
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.TermDist Matrix

/-! ### Binary quartic forms -/

/-- A binary quartic vanishing at five pairwise non-proportional points is zero. -/
theorem quartic {ι F : Type*} [Field F] (s : Finset ι) (hs : s.card = 5) (l m : ι → F)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → l i * m j - l j * m i ≠ 0)
    (a : Fin 5 → F) (h : ∀ i ∈ s, ∑ r : Fin 5, a r * (l i ^ (4 - r.val) * m i ^ r.val) = 0) :
    a = 0 := by
  classical
  let p : Polynomial F := Polynomial.C (a 0) + Polynomial.C (a 1) * Polynomial.X +
    Polynomial.C (a 2) * Polynomial.X ^ 2 + Polynomial.C (a 3) * Polynomial.X ^ 3 +
    Polynomial.C (a 4) * Polynomial.X ^ 4
  have hroot : ∀ i ∈ s, l i ≠ 0 → p.eval (m i / l i) = 0 := by
    intro i hi hl
    have hi' := h i hi
    simp only [Fin.sum_univ_five, Fin.val_zero, Fin.val_one, Fin.val_two] at hi'
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have : (a 0 + a 1 * (m i / l i) + a 2 * (m i / l i) ^ 2 + a 3 * (m i / l i) ^ 3 +
        a 4 * (m i / l i) ^ 4) * l i ^ 4 = 0 := by
      field_simp
      norm_num at hi'
      linear_combination hi'
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ hl)
  set s0 := s.filter (fun i => l i ≠ 0) with hs0
  set T := s0.image (fun i => m i / l i) with hT
  have hTc : T.card = s0.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    simp only [hs0, Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
    by_contra hne
    apply hd i hi.1 j hj.1 hne
    have := (div_eq_div_iff hi.2 hj.2).1 hij
    linear_combination -this
  have hz : (s.filter (fun i => ¬ l i ≠ 0)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro i hi j hj
    simp only [Finset.mem_filter, not_not] at hi hj
    by_contra hne
    apply hd i hi.1 j hj.1 hne
    rw [hi.2, hj.2]; ring
  have hsum : s0.card + (s.filter (fun i => ¬ l i ≠ 0)).card = s.card :=
    Finset.card_filter_add_card_filter_not (s := s) (fun i => l i ≠ 0)
  have hTe : ∀ t ∈ T, p.eval t = 0 := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    simp only [hs0, Finset.mem_filter] at hi
    exact hroot i hi.1 hi.2
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p T hTe
    by_cases h0 : ∃ i ∈ s, l i = 0
    · obtain ⟨i, hi, hl⟩ := h0
      obtain ⟨j, hj, hji⟩ : ∃ j ∈ s, j ≠ i := by
        by_contra hc
        push Not at hc
        have : s.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy => (hc x hx).trans (hc y hy).symm
        omega
      have hm : m i ≠ 0 := by
        intro hm
        apply hd i hi j hj hji.symm
        rw [hl, hm]; ring
      have h4 : a 4 = 0 := by
        have hi' := h i hi
        simp only [Fin.sum_univ_five, hl] at hi'
        norm_num at hi'
        rcases hi' with h' | h'
        · exact h'
        · exact absurd h' hm
      have hp3 : p.natDegree ≤ 3 := by
        simp only [p, h4, map_zero, zero_mul, add_zero]
        compute_degree
      omega
    · push Not at h0
      have : s0 = s := Finset.filter_true_of_mem h0
      have hp4 : p.natDegree ≤ 4 := by
        simp only [p]
        compute_degree
      rw [hTc, this]; omega
  funext r
  have hc := fun k => congrArg (fun q : Polynomial F => q.coeff k) hp0
  fin_cases r
  · simpa [p] using hc 0
  · simpa [p] using hc 1
  · simpa [p] using hc 2
  · simpa [p] using hc 3
  · simpa [p] using hc 4

/-! ### Two-dimensional orthogonal complements -/

theorem lin_indep {K : Type*} [Field K] {U W : Fin 3 → K} (h : U ⨯₃ W ≠ 0) :
    LinearIndependent K ![U, W] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : (s • U + t • W) ⨯₃ W = s • (U ⨯₃ W) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, cross_self,
      smul_zero, add_zero]
  have h2 : U ⨯₃ (s • U + t • W) = t • (U ⨯₃ W) := by
    simp only [map_add, map_smul, cross_self, smul_zero, zero_add]
  rw [hst, map_zero, LinearMap.zero_apply] at h1
  rw [hst, map_zero] at h2
  exact ⟨(smul_eq_zero.1 h1.symm).resolve_right h, (smul_eq_zero.1 h2.symm).resolve_right h⟩

theorem span2 {K : Type*} [Field K] {x U W y : Fin 3 → K} (hx : x ≠ 0) (hU : x ⬝ᵥ U = 0)
    (hW : x ⬝ᵥ W = 0) (hUW : U ⨯₃ W ≠ 0) (hy : x ⬝ᵥ y = 0) :
    ∃ c : K × K, y = c.1 • U + c.2 • W := by
  classical
  let f : (Fin 3 → K) →ₗ[K] K :=
    { toFun := fun z => x ⬝ᵥ z
      map_add' := fun a b => dotProduct_add x a b
      map_smul' := fun c a => by simp [dotProduct_smul] }
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hc; push Not at hc; exact hx (funext hc)
  have hsurj : Function.Surjective f := by
    intro t
    refine ⟨(t / x k) • Pi.single k 1, ?_⟩
    simp [f, hk]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at hrank
  have hli := lin_indep hUW
  have hspan := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at hspan
  have hle : Submodule.span K (Set.range ![U, W]) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    fin_cases i
    · simpa [f] using hU
    · simpa [f] using hW
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hmem : y ∈ Submodule.span K (Set.range ![U, W]) := by
    rw [heq]; simpa [f] using hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  refine ⟨(c 0, c 1), ?_⟩
  rw [← hc, Fin.sum_univ_two]
  rfl

/-! ### Endpoints and the artificial orientation -/

theorem pe_ne_le (q : Edge) : pointEnd q ≠ lineEnd q := fun h => by
  have := congrArg Fin.val h
  have := pe_lt q
  have := le_ge q
  omega

theorem head_tail (q : Edge) :
    (head q = pointEnd q ∧ tail q = lineEnd q) ∨ (head q = lineEnd q ∧ tail q = pointEnd q) := by
  unfold head tail earlier later
  split_ifs <;> simp

theorem head_ne_tail (q : Edge) : head q ≠ tail q := by
  rcases head_tail q with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact pe_ne_le q
  · exact (pe_ne_le q).symm

theorem incident_iff (v : Vertex) (q : Edge) : incident v q ↔ head q = v ∨ tail q = v := by
  unfold incident
  rcases head_tail q with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
    constructor <;> rintro (h | h) <;> subst h <;> simp

theorem known_iff (v : Vertex) (q : Edge) : q ∈ knownPositions v ↔
    (head q = v ∧ q ∉ J) ∨ (tail q = v ∧ q ∈ C) := by
  have hC : C ⊆ deleted := balanced_orientation.2.2.2.2.2.2.2.1
  have hJ : J ⊆ deleted := balanced_orientation.2.2.2.2.2.2.2.2.1
  have hCJ : Disjoint C J := balanced_orientation.2.2.2.2.2.2.2.2.2.1
  have hC' : q ∈ C → q ∈ deleted := fun h => hC h
  have hJ' : q ∈ J → q ∈ deleted := fun h => hJ h
  have hd : q ∈ C → q ∉ J := fun h1 h2 => Finset.disjoint_left.1 hCJ h1 h2
  simp only [knownPositions, Finset.mem_filter, Finset.mem_univ, true_and, physical, B,
    Finset.mem_sdiff, Finset.mem_union, incident_iff]
  generalize (q ∈ C) = pC at *
  generalize (q ∈ J) = pJ at *
  generalize (q ∈ deleted) = pD at *
  generalize (head q = v) = a at *
  generalize (tail q = v) = b at *
  tauto

theorem incident_of_known {v : Vertex} {q : Edge} (h : q ∈ knownPositions v) : incident v q := by
  rw [incident_iff]
  rw [known_iff] at h
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem known_card (v : Vertex) : (knownPositions v).card = 5 := by
  have hv := (balanced_orientation.2.2.2.2.2.2.2.2.2.2.2.2 v)
  have hin := hv.1
  have hbal := hv.2.2
  have e1 : knownPositions v =
      (Finset.univ.filter fun q => head q = v ∧ q ∉ J) ∪ C.filter (tail · = v) := by
    ext q
    simp only [known_iff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
  have d1 : Disjoint (Finset.univ.filter fun q => head q = v ∧ q ∉ J) (C.filter (tail · = v)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact head_ne_tail q (h1.2.1.trans h2.2.symm)
  have e2 : Finset.univ.filter (head · = v) =
      (Finset.univ.filter fun q => head q = v ∧ q ∉ J) ∪ J.filter (head · = v) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : q ∈ J
    · simp [hq]
    · simp [hq]
  have d2 : Disjoint (Finset.univ.filter fun q => head q = v ∧ q ∉ J) (J.filter (head · = v)) := by
    rw [Finset.disjoint_left]
    intro q h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact h1.2.2 h2.1
  have c2 := congrArg Finset.card e2
  rw [Finset.card_union_of_disjoint d2] at c2
  rw [e1, Finset.card_union_of_disjoint d1]
  simp only [inDegree, outDegree] at hin hbal
  omega

/-! ### Neighbours of a vertex -/

/-- The index of the other endpoint of `q`, seen from `v`. -/
def nb (v : Vertex) (q : Edge) : Fin 91 := if v.val < 91 then (edgePair q).2 else (edgePair q).1

theorem neighborOn_eq (v : Vertex) (q : Edge) : neighborOn v q = triple (nb v q) := by
  unfold neighborOn nb
  split_ifs <;> rfl

theorem ep_eq {v : Vertex} {q : Edge} (h : incident v q) :
    edgePair q = if v.val < 91 then (vertexTriple v, nb v q) else (nb v q, vertexTriple v) := by
  have h1 := pe_lt q
  have h2 := le_ge q
  rcases h with rfl | rfl
  · rw [if_pos h1]
    simp only [nb, if_pos h1]
    refine Prod.ext (Fin.ext ?_) rfl
    show _ = (edgePair q).1.val % 91
    rw [Nat.mod_eq_of_lt (edgePair q).1.isLt]
  · have h3 : ¬ (lineEnd q).val < 91 := by omega
    rw [if_neg h3]
    simp only [nb, if_neg h3]
    refine Prod.ext rfl (Fin.ext ?_)
    show _ = (91 + (edgePair q).2.val) % 91
    have := (edgePair q).2.isLt
    omega

theorem dot_comm' (x y : Triple) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem dot_nb {v : Vertex} {q : Edge} (h : incident v q) :
    dot (triple (vertexTriple v)) (triple (nb v q)) = 0 := by
  have e := inc q
  have he := ep_eq h
  by_cases hv : v.val < 91
  · rw [if_pos hv] at he
    rw [he] at e
    exact e
  · rw [if_neg hv] at he
    rw [he] at e
    rw [dot_comm']
    exact e

theorem nb_inj {v : Vertex} {q q' : Edge} (h : incident v q) (h' : incident v q')
    (e : nb v q = nb v q') : q = q' :=
  balanced_orientation.2.2.1 (by rw [ep_eq h, ep_eq h', e])

theorem triple_ne_zero (i : Fin 91) : triple i ≠ 0 := by
  intro h
  rcases nrm_triple i with ⟨-, -, h2⟩ | ⟨-, h1⟩ | h0
  · rw [h] at h2; exact zero_ne_one h2
  · rw [h] at h1; exact zero_ne_one h1
  · rw [h] at h0; exact zero_ne_one h0

/-! ### The basis `U, W` of the orthogonal complement -/

theorem mem_nt {v : Vertex} {j : Fin 91} :
    j ∈ neighborTriples v ↔ dot (triple (vertexTriple v)) (triple j) = 0 := by
  simp [neighborTriples]

theorem nt_len (v : Vertex) : 2 ≤ (neighborTriples v).length := by
  obtain ⟨q, hq, q', hq', hne⟩ :=
    Finset.one_lt_card.1 (by rw [known_card]; norm_num : 1 < (knownPositions v).card)
  have hi := incident_of_known hq
  have hi' := incident_of_known hq'
  have hne' : nb v q ≠ nb v q' := fun e => hne (nb_inj hi hi' e)
  have : 1 < (neighborTriples v).toFinset.card := Finset.one_lt_card.2
    ⟨_, List.mem_toFinset.2 (mem_nt.2 (dot_nb hi)), _,
      List.mem_toFinset.2 (mem_nt.2 (dot_nb hi')), hne'⟩
  have := List.toFinset_card_le (neighborTriples v)
  omega

theorem basis_facts (v : Vertex) :
    dot (triple (vertexTriple v)) (basisU v) = 0 ∧ dot (triple (vertexTriple v)) (basisW v) = 0 ∧
      basisU v ⨯₃ basisW v ≠ 0 := by
  have hl := nt_len v
  have hnd : (neighborTriples v).Nodup := (List.nodup_finRange 91).filter _
  have g0 : (neighborTriples v).getD 0 0 = (neighborTriples v)[0] :=
    List.getD_eq_getElem _ _ (by omega)
  have g1 : (neighborTriples v).getD 1 0 = (neighborTriples v)[1] :=
    List.getD_eq_getElem _ _ (by omega)
  unfold basisU basisW
  rw [g0, g1]
  refine ⟨mem_nt.1 (List.getElem_mem _), mem_nt.1 (List.getElem_mem _), fun h => ?_⟩
  have := triple_inj (cross_zero_eq (nrm_triple _) (nrm_triple _) h)
  have := (hnd.getElem_inj_iff).1 this
  omega

theorem coord_spec {v : Vertex} {q : Edge} (h : incident v q) :
    neighborOn v q = (coordinates v q).1 • basisU v + (coordinates v q).2 • basisW v := by
  obtain ⟨hU, hW, hUW⟩ := basis_facts v
  have hex : ∃ c : F9 × F9, neighborOn v q = c.1 • basisU v + c.2 • basisW v := by
    rw [neighborOn_eq]
    exact span2 (triple_ne_zero _) hU hW hUW (dot_nb h)
  unfold coordinates
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem cross_comb {K : Type*} [CommRing K] (a b a' b' : K) (U W : Fin 3 → K) :
    (a • U + b • W) ⨯₃ (a' • U + b' • W) = (a * b' - a' * b) • (U ⨯₃ W) := by
  funext k
  fin_cases k <;> simp [cross_apply] <;> ring

theorem det_ne {v : Vertex} {q q' : Edge} (h : incident v q) (h' : incident v q') (hne : q ≠ q') :
    (coordinates v q).1 * (coordinates v q').2 - (coordinates v q').1 * (coordinates v q).2 ≠ 0 := by
  intro hd
  apply hne
  apply nb_inj h h'
  apply triple_inj
  apply cross_zero_eq (nrm_triple _) (nrm_triple _)
  rw [← neighborOn_eq, ← neighborOn_eq, coord_spec h, coord_spec h', cross_comb, hd, zero_smul]

theorem three_eq_zero : (3 : F9) = 0 := by
  ext <;> simp <;> decide

theorem cube_sub (x y : F9) : (x - y) ^ 3 = x ^ 3 - y ^ 3 := by
  linear_combination (-(x ^ 2 * y) + x * y ^ 2) * three_eq_zero

theorem local_unique' (v : Vertex) (a b : Coefficients)
    (h : ∀ q ∈ knownPositions v, localEvaluation v a q = localEvaluation v b q) : a = b := by
  let l : Edge → F9 := fun q =>
    if v.val < 91 then (coordinates v q).1 else (coordinates v q).1 ^ 3
  let m : Edge → F9 := fun q =>
    if v.val < 91 then (coordinates v q).2 else (coordinates v q).2 ^ 3
  have hw : ∀ q r, localWeight v q r = l q ^ (4 - r.val) * m q ^ r.val := fun q r => rfl
  have key := quartic (knownPositions v) (known_card v) l m ?_ (a - b) ?_
  · exact sub_eq_zero.1 key
  · intro i hi j hj hij
    have d := det_ne (incident_of_known hi) (incident_of_known hj) hij
    simp only [l, m]
    split_ifs
    · exact d
    · rw [← mul_pow, ← mul_pow, ← cube_sub]
      exact pow_ne_zero 3 d
  · intro i hi
    have := h i hi
    simp only [localEvaluation, LinearMap.coe_mk, AddHom.coe_mk,
      if_pos (incident_of_known hi)] at this
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, ← hw, this, sub_self]

end MultipleUnicast.Counterexample.Dev.RILocal

namespace MultipleUnicast.Counterexample.Dev.RI
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.RILocal

/-- Local uniqueness: the five available positions at `v` determine the local coefficients. -/
theorem local_unique (v : Vertex) (a b : Coefficients)
    (h : ∀ q ∈ knownPositions v, localEvaluation v a q = localEvaluation v b q) : a = b :=
  local_unique' v a b h

/-- The local interpolation API of the Protocol bundle. -/
theorem localInterpolation : LocalInterpolation := by
  intro v
  refine ⟨known_card v, ?_⟩
  let E : Coefficients →ₗ[F9] ({q : Edge // q ∈ knownPositions v} → F9) :=
    (LinearMap.funLeft F9 F9 (Subtype.val : {q : Edge // q ∈ knownPositions v} → Edge)) ∘ₗ
      localEvaluation v
  have hinj : Function.Injective E := by
    intro a b hab
    apply local_unique' v a b
    intro q hq
    exact congrFun hab ⟨q, hq⟩
  have hfr : Module.finrank F9 Coefficients =
      Module.finrank F9 ({q : Edge // q ∈ knownPositions v} → F9) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    simp [known_card]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  let e := LinearEquiv.ofBijective E ⟨hinj, hsurj⟩
  have hE : ∀ y, E (e.symm y) = y := fun y => e.apply_symm_apply y
  refine ⟨e.symm.toLinearMap, fun y q => congrFun (hE y) q, fun y => ?_⟩
  have hex : ∃ a : Coefficients, ∀ q ∈ knownPositions v, localEvaluation v a q = y q :=
    ⟨e.symm (fun q => y q.val), fun q hq => congrFun (hE _) ⟨q, hq⟩⟩
  unfold interpolate
  rw [dif_pos hex]
  apply local_unique'
  intro q hq
  rw [Classical.choose_spec hex q hq]
  exact (congrFun (hE (fun q => y q.val)) ⟨q, hq⟩).symm

end MultipleUnicast.Counterexample.Dev.RI
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false

namespace MultipleUnicast.Counterexample.Dev.RIGlobal
open MultipleUnicast.Counterexample

/-! ### The processing order -/

theorem perm : processingOrder.Perm (List.finRange 182) :=
  balanced_orientation.2.2.2.1

theorem mem_order (v : Vertex) : v ∈ processingOrder :=
  perm.mem_iff.2 (List.mem_finRange v)

theorem nodup_order : processingOrder.Nodup :=
  perm.nodup_iff.2 (List.nodup_finRange 182)

theorem length_order : processingOrder.length = 182 := by
  rw [perm.length_eq, List.length_finRange]

theorem position_lt (v : Vertex) : position v < 182 := by
  rw [← length_order]; exact List.idxOf_lt_length_of_mem (mem_order v)

theorem position_inj {u v : Vertex} (h : position u = position v) : u = v :=
  (List.idxOf_inj (mem_order u)).1 h

theorem position_getD (n : ℕ) (hn : n < 182) : position (processingOrder.getD n 0) = n := by
  have hn' : n < processingOrder.length := length_order ▸ hn
  unfold position
  rw [List.getD_eq_getElem _ _ hn']
  exact nodup_order.idxOf_getElem n hn'

/-! ### Orientation facts -/

theorem pe_ne_le (q : Edge) : pointEnd q ≠ lineEnd q := by
  intro h
  have h1 : (pointEnd q).val < 91 := (edgePair q).1.isLt
  have h2 : 91 ≤ (lineEnd q).val := Nat.le_add_right _ _
  rw [h] at h1; omega

theorem incident_tail (q : Edge) : incident (tail q) q := by
  unfold tail earlier later incident; split_ifs <;> simp

theorem incident_head (q : Edge) : incident (head q) q := by
  unfold head earlier later incident; split_ifs <;> simp

theorem pos_tail_lt (q : Edge) (hq : q ∉ deleted) : position (tail q) < position (head q) := by
  unfold tail head earlier later
  rw [if_neg hq, if_neg hq]
  split_ifs with h
  · exact h
  · have hne : position (pointEnd q) ≠ position (lineEnd q) := fun h' => pe_ne_le q (position_inj h')
    omega

theorem known_incident {v : Vertex} {p : Edge} (hp : p ∈ knownPositions v) : incident v p := by
  unfold knownPositions at hp
  rcases (Finset.mem_filter.1 hp).2 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · exact h ▸ incident_head p
  · exact h ▸ incident_head p
  · exact h

/-! ### Local coefficients of elements of `W` -/

theorem coeffs {w : Edge → F9} (hw : w ∈ W) (v : Vertex) :
    ∃ a : Coefficients, ∀ q, incident v q → localEvaluation v a q = w q := by
  have h := (Submodule.mem_iInf _).1 hw v
  rw [Submodule.mem_comap, LinearMap.mem_range] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun q hq => ?_⟩
  rw [ha]
  show (if incident v q then w q else 0) = w q
  rw [if_pos hq]

/-- Interpolating data that agrees with `w ∈ W` on the known positions of `v`
reproduces `w` on every edge incident to `v`. -/
theorem determined {w : Edge → F9} (hw : w ∈ W) (v : Vertex) (y : Edge → F9)
    (hy : ∀ p ∈ knownPositions v, y p = w p) :
    ∀ q, incident v q → localEvaluation v (interpolate v y) q = w q := by
  obtain ⟨a, ha⟩ := coeffs hw v
  have hex : ∃ b : Coefficients, ∀ q ∈ knownPositions v, localEvaluation v b q = y q :=
    ⟨a, fun p hp => (ha p (known_incident hp)).trans (hy p hp).symm⟩
  have hI : interpolate v y = a := by
    unfold interpolate
    rw [dif_pos hex]
    apply Dev.RI.local_unique
    intro p hp
    rw [Classical.choose_spec hex p hp, ha p (known_incident hp), hy p hp]
  intro q hq
  rw [hI, ha q hq]

theorem WC_W (w : WC) : w.val ∈ W := (Submodule.mem_inf.1 w.prop).1

theorem WC_C (w : WC) (q : Edge) (hq : q ∈ C) : w.val q = 0 := by
  have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 w.prop).2 ⟨q, hq⟩
  rw [LinearMap.mem_ker] at h
  exact h

theorem not_deleted_of_physical {p : Edge} (hp : p ∈ physical) : p ∉ deleted :=
  (Finset.mem_sdiff.1 hp).2

theorem not_physical_of_B {p : Edge} (hp : p ∈ B) : p ∉ physical := fun h =>
  not_deleted_of_physical h (Finset.mem_sdiff.1 hp).1

/-! ### Injectivity -/

theorem restriction_injective : Function.Injective restriction := by
  rw [injective_iff_map_eq_zero]
  intro w hw0
  have hB : ∀ q ∈ B, w.val q = 0 := fun q hq => congrFun hw0 ⟨q, hq⟩
  have hW := WC_W w
  have main : ∀ n, ∀ q, position (tail q) = n → w.val q = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro q hqn
      have hy : ∀ p ∈ knownPositions (tail q), (0 : Edge → F9) p = w.val p := by
        intro p hp
        unfold knownPositions at hp
        rcases (Finset.mem_filter.1 hp).2 with ⟨hph, hh⟩ | ⟨hb, _⟩ | ⟨hc, _⟩
        · have := pos_tail_lt p (not_deleted_of_physical hph)
          rw [hh] at this
          exact (ih _ (hqn ▸ this) p rfl).symm
        · exact (hB p hb).symm
        · exact (WC_C w p hc).symm
      have h1 := determined hW (tail q) 0 hy q (incident_tail q)
      have h2 := determined (Submodule.zero_mem W) (tail q) 0 (fun _ _ => rfl) q (incident_tail q)
      rw [← h1, h2]; rfl
  apply Subtype.ext
  funext q
  exact main _ q rfl

/-! ### Dimension count -/

theorem finrank_WC : 157 ≤ Module.finrank F9 WC := by
  have hCcard : C.card = 9 := balanced_orientation.2.2.2.2.2.1
  let φ : W →ₗ[F9] ({q : Edge // q ∈ C} → F9) :=
    LinearMap.pi fun q => (LinearMap.proj q.val).comp W.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank F9 (LinearMap.range φ) ≤ 9 := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hCcard]
  have hdim := dimension_bound
  let ψ : LinearMap.ker φ →ₗ[F9] WC :=
    LinearMap.codRestrict WC (W.subtype.comp (LinearMap.ker φ).subtype) (by
      intro c
      refine Submodule.mem_inf.2 ⟨c.val.prop, (Submodule.mem_iInf _).2 fun q => ?_⟩
      rw [LinearMap.mem_ker]
      have := congrFun (LinearMap.mem_ker.1 c.prop) q
      exact this)
  have hψ : Function.Injective ψ := by
    intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hle := LinearMap.finrank_le_finrank_of_injective hψ
  omega

theorem restriction_bijective : Function.Bijective restriction := by
  have hBcard : B.card = 157 := balanced_orientation.2.2.2.2.2.2.2.2.2.2.1
  have hS : Module.finrank F9 (Session → F9) = 157 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hBcard]
  have hle := LinearMap.finrank_le_finrank_of_injective restriction_injective
  have heq : Module.finrank F9 WC = Module.finrank F9 (Session → F9) := by
    have := finrank_WC; omega
  exact ⟨restriction_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 restriction_injective⟩

/-! ### The execution computes the preimage -/

theorem run_eq (x : Input) (w : WC) (hx : restriction w = x) :
    ∀ n, n ≤ 182 → ∀ q, run n x q = if position (tail q) < n then w.val q else 0 := by
  intro n
  induction n with
  | zero => intro _ q; simp [run]
  | succ n ih =>
    intro hn q
    have ih' := ih (by omega)
    set v := processingOrder.getD n 0 with hv
    have hpv : position v = n := position_getD n (by omega)
    have hy : ∀ p ∈ knownPositions v, available v x (run n x) p = w.val p := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      unfold available
      by_cases hc : p ∈ C
      · rw [if_pos hc]; exact (WC_C w p hc).symm
      rw [if_neg hc]
      by_cases hb : p ∈ B
      · rw [dif_pos hb]
        have hh : head p = v := by
          rcases hp' with ⟨hph, _⟩ | ⟨_, hh⟩ | ⟨hc', _⟩
          · exact absurd hph (not_physical_of_B hb)
          · exact hh
          · exact absurd hc' hc
        rw [if_pos hh, ← hx]; rfl
      · rw [dif_neg hb]
        rcases hp' with ⟨hph, hh⟩ | ⟨hb', _⟩ | ⟨hc', _⟩
        · have := pos_tail_lt p (not_deleted_of_physical hph)
          rw [hh, hpv] at this
          rw [ih', if_pos this]
        · exact absurd hb' hb
        · exact absurd hc' hc
    have hstep : run (n + 1) x q =
        if tail q = v then localEvaluation v (interpolate v (available v x (run n x))) q
        else run n x q := rfl
    rw [hstep]
    by_cases ht : tail q = v
    · rw [if_pos ht, determined (WC_W w) v _ hy q (ht ▸ incident_tail q), if_pos]
      rw [ht, hpv]; omega
    · rw [if_neg ht, ih']
      have hne : position (tail q) ≠ n := fun h => ht (position_inj (h.trans hpv.symm))
      by_cases hlt : position (tail q) < n
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

theorem execution_eq (x : Input) (w : WC) (hx : restriction w = x) : execution x = w.val := by
  funext q
  unfold execution
  rw [run_eq x w hx 182 le_rfl q, if_pos (position_lt _)]

end MultipleUnicast.Counterexample.Dev.RIGlobal

namespace MultipleUnicast.Counterexample
open Dev.RIGlobal

theorem chk_restriction_isomorphism :
    Function.Bijective restriction ∧ LocalInterpolation ∧
    ∀ x : Input, ∃! w : WC,
      restriction w = x ∧ execution x = w.val := by
  refine ⟨restriction_bijective, Dev.RI.localInterpolation, fun x => ?_⟩
  obtain ⟨w, hw⟩ := restriction_bijective.2 x
  exact ⟨w, ⟨hw, execution_eq x w hw⟩, fun w' hw' =>
    restriction_injective (hw'.1.trans hw.symm)⟩

end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_restriction_isomorphism := @MultipleUnicast.Counterexample.chk_restriction_isomorphism
