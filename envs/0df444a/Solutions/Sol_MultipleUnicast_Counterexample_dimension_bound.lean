-- Prove2me | solution 1 for MultipleUnicast.Counterexample.dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:29:55.164809+00:00
-- url     : https://prove2.me/submissions/928d7aca-1ef4-4d53-89d8-40d94f4f9333

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph
import Definitions.Def_MultipleUnicast_Counterexample_Protocol
import Theorems.Thm_MultipleUnicast_Counterexample_balanced_orientation
import Definitions.Def_MultipleUnicast_Counterexample_LocalSpace

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

/-! The incidence rows of PG(2,9), checked in ten small kernel computations. -/

namespace MultipleUnicast.Counterexample.Dev.IncRows
open MultipleUnicast.Counterexample

end MultipleUnicast.Counterexample.Dev.IncRows
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false
namespace MultipleUnicast.Counterexample.Dev.Bal
open MultipleUnicast.Counterexample


end MultipleUnicast.Counterexample.Dev.Bal
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

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

theorem three_eq_zero : (3 : F9) = 0 := by
  ext <;> simp <;> decide

end MultipleUnicast.Counterexample.Dev.RILocal

namespace MultipleUnicast.Counterexample.Dev.RI
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.RILocal

end MultipleUnicast.Counterexample.Dev.RI
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
open scoped Classical

/-! Objects of the dimension bound (paper, Appendix B): the 166 retained monomials `X^a Y^b` of bidegree
(4,4) divisible by neither `X₀Y₀³` nor `X₁³Y₁`, the evaluation `h(x, y)` of a combination of them, and the
substituted polynomial `Q_h(Z) = h(A(Z), Z^(3))` with `A(Z) = Z × Z^(9)`. -/

namespace MultipleUnicast.Counterexample.Dev.Dim
open MultipleUnicast.Counterexample MvPolynomial

/-- An exponent triple, each exponent at most 4. -/
abbrev E3 := Fin 3 → Fin 5

def tot (a : E3) : ℕ := (a 0 : ℕ) + (a 1 : ℕ) + (a 2 : ℕ)

/-- Bidegree (4,4) and divisible by neither `X₀Y₀³` nor `X₁³Y₁`. -/
def retained (m : E3 × E3) : Prop :=
  tot m.1 = 4 ∧ tot m.2 = 4 ∧ ¬ (1 ≤ (m.1 0 : ℕ) ∧ 3 ≤ (m.2 0 : ℕ)) ∧
    ¬ (3 ≤ (m.1 1 : ℕ) ∧ 1 ≤ (m.2 1 : ℕ))

instance : DecidablePred retained := fun m => by unfold retained; infer_instance

abbrev Mon := {m : E3 × E3 // retained m}

/-- Coordinatewise cube `x^(3)`. -/
def cube3 (x : Triple) : Triple := fun k => x k ^ 3

/-- The monomial `x^a = x₀^a₀ x₁^a₁ x₂^a₂` evaluated at a triple. -/
def mon (a : E3) (x : Triple) : F9 := x 0 ^ (a 0 : ℕ) * x 1 ^ (a 1 : ℕ) * x 2 ^ (a 2 : ℕ)

/-- `h(x, y) = Σ_m c_m x^a y^b`. -/
def hval (c : Mon → F9) (x y : Triple) : F9 := ∑ m : Mon, c m * mon m.val.1 x * mon m.val.2 y

/-- The coordinates of `A(Z) = Z × Z^(9)`, as polynomials in `Z₀, Z₁, Z₂` (formal: `Z^9` is not reduced). -/
noncomputable def Acoord : Fin 3 → MvPolynomial (Fin 3) F9 :=
  ![X 1 * X 2 ^ 9 - X 2 * X 1 ^ 9, X 2 * X 0 ^ 9 - X 0 * X 2 ^ 9, X 0 * X 1 ^ 9 - X 1 * X 0 ^ 9]

/-- `P^a = P₀^a₀ P₁^a₁ P₂^a₂` for a triple of polynomials. -/
noncomputable def pmon (a : E3) (P : Fin 3 → MvPolynomial (Fin 3) F9) : MvPolynomial (Fin 3) F9 :=
  P 0 ^ (a 0 : ℕ) * P 1 ^ (a 1 : ℕ) * P 2 ^ (a 2 : ℕ)

/-- `Q_h(Z) = h(A(Z), Z^(3)) = Σ_m c_m A(Z)^a (Z^(3))^b`. -/
noncomputable def Qpoly (c : Mon → F9) : MvPolynomial (Fin 3) F9 :=
  ∑ m : Mon, MvPolynomial.C (c m) * pmon m.val.1 Acoord * pmon m.val.2 (fun k => X k ^ 3)

/-- The edge assignment `w_m(p, ℓ) = (p^(3))^a ℓ^b` of a retained monomial. -/
def wvec (m : Mon) (q : Edge) : F9 :=
  mon m.val.1 (cube3 (triple (edgePair q).1)) * mon m.val.2 (triple (edgePair q).2)

end MultipleUnicast.Counterexample.Dev.Dim
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false
open scoped Classical

/-! Paper, Appendix B, (2) ⇒ (5): if `h(p^(3), ℓ) = 0` at every incident pair, then `Q_h = 0`.

Route. For a normalized `x` and `e` with `x · e = 1`, the substitution `φ : Z_i ↦ Z_i − e_i (x · Z)`
maps `Z` onto the plane `x · Z = 0`; `P − φ P` is always divisible by `x · Z`. On the plane,
`A(Z)` is a multiple `λ x` (both `Z` and `Z^(9)` are orthogonal to `x`), so `φ Q_h = λ⁴ ψ(G)` where
`ψ` cubes the variables and `G(z) = h(x, z − e^(3) (x^(3) · z))`; `G` has degree `≤ 4` and vanishes on
`F9³` by hypothesis, so `G = 0` (combinatorial Nullstellensatz). Peeling the 91 pairwise
non-proportional forms `x · Z` gives a divisor of degree 91 of `Q_h`, of degree `≤ 52`. -/

namespace MultipleUnicast.Counterexample.Dev.DimVanish
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Dim
open MultipleUnicast.Counterexample.Dev.TermDist MvPolynomial Matrix

abbrev R := MvPolynomial (Fin 3) F9

/-! ### Arithmetic in characteristic three -/

theorem h3F : (3 : F9) = 0 := by
  ext <;> simp <;> decide

theorem h3R : (3 : R) = 0 := by
  calc (3 : R) = MvPolynomial.C (3 : F9) := (map_ofNat _ 3).symm
    _ = 0 := by rw [h3F, map_zero]

theorem cube_add3 {K : Type*} [CommRing K] (h3 : (3 : K) = 0) (a b c : K) :
    (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 := by
  linear_combination (a ^ 2 * b + a ^ 2 * c + a * b ^ 2 + b ^ 2 * c + a * c ^ 2 + b * c ^ 2
    + 2 * a * b * c) * h3

theorem cube_sub2 {K : Type*} [CommRing K] (h3 : (3 : K) = 0) (a b : K) :
    (a - b) ^ 3 = a ^ 3 - b ^ 3 := by
  linear_combination (-(a ^ 2 * b) + a * b ^ 2) * h3

theorem pow_nine (a : F9) : a ^ 9 = a := by
  revert a; decide

theorem cube_cube (u : Triple) : cube3 (cube3 u) = u := by
  funext k; simp only [cube3, ← pow_mul]; exact pow_nine _

/-! ### Linear forms -/

/-- The linear form `v · Z`. -/
noncomputable def lf (v : Triple) : R := MvPolynomial.C (v 0) * X 0 + MvPolynomial.C (v 1) * X 1 + MvPolynomial.C (v 2) * X 2

/-- `v · Z^(n)`. -/
noncomputable def lfp (v : Triple) (n : ℕ) : R :=
  MvPolynomial.C (v 0) * X 0 ^ n + MvPolynomial.C (v 1) * X 1 ^ n + MvPolynomial.C (v 2) * X 2 ^ n

theorem lf_cube (v : Triple) : lf v ^ 3 = lfp (cube3 v) 3 := by
  rw [lf, cube_add3 h3R]; simp only [lfp, cube3, mul_pow, map_pow]

theorem lf_nine (v : Triple) : lf v ^ 9 = lfp v 9 := by
  rw [show 9 = 3 * 3 from rfl, pow_mul, lf_cube, lfp, cube_add3 h3R]
  simp only [lfp, cube3, mul_pow, ← map_pow, ← pow_mul]
  norm_num [pow_nine]

theorem coeff_lf (v : Triple) (k : Fin 3) : coeff (Finsupp.single k 1) (lf v) = v k := by
  fin_cases k <;> simp [lf, coeff_X, Finsupp.single_eq_single_iff]

theorem lf_ne_zero {v : Triple} (hv : v ≠ 0) : lf v ≠ 0 := by
  intro h
  apply hv
  funext k
  rw [← coeff_lf v k, h, coeff_zero]; rfl

theorem one_le_deg_lf {v : Triple} (hv : v ≠ 0) : 1 ≤ (lf v).totalDegree := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra hc; push Not at hc; exact hv (funext hc)
  have hs : Finsupp.single k 1 ∈ (lf v).support := by
    rw [mem_support_iff, coeff_lf]; exact hk
  have := le_totalDegree hs
  simpa [Finsupp.sum_single_index] using this

/-! ### The substitution onto a plane, and divisibility -/

/-- `Z_i ↦ Z_i − e_i (x · Z)`. -/
noncomputable def gv (x e : Triple) (i : Fin 3) : R := X i - MvPolynomial.C (e i) * lf x

noncomputable def phi (x e : Triple) : R →ₐ[F9] R := bind₁ (gv x e)

theorem sub_phi_dvd (x e : Triple) (P : R) : lf x ∣ P - phi x e P := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have hcomp : (Ideal.Quotient.mkₐ F9 (Ideal.span {lf x})).comp (phi x e) =
      Ideal.Quotient.mkₐ F9 (Ideal.span {lf x}) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, phi, bind₁_X_right, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-MvPolynomial.C (e i), by simp [gv]; ring⟩
  have := congrArg (fun f => f P) hcomp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
  exact this.symm

theorem phi_lf (x e y : Triple) :
    phi x e (lf y) = lf (fun k => y k - dot y e * x k) := by
  simp only [phi, lf, map_add, map_mul, bind₁_X_right, bind₁_C_right, gv, dot,
    Fin.sum_univ_three, map_sub]
  ring

/-- Peeling: if `φ_i P = 0` for every `i ∈ S` and the forms are pairwise non-proportional,
the product of the forms divides `P`. -/
theorem peel (t e : Fin 91 → Triple)
    (hd : ∀ i j, i ≠ j → (fun k => t j k - dot (t j) (e i) * t i k) ≠ 0) :
    ∀ (S : Finset (Fin 91)) (P : R), (∀ i ∈ S, phi (t i) (e i) P = 0) →
      (∏ i ∈ S, lf (t i)) ∣ P := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro P _; simp
  | insert a S ha ih =>
    intro P hP
    obtain ⟨P', hP'⟩ : lf (t a) ∣ P := by
      have := sub_phi_dvd (t a) (e a) P
      rwa [hP a (Finset.mem_insert_self a S), sub_zero] at this
    rw [Finset.prod_insert ha, hP']
    refine mul_dvd_mul_left _ (ih P' fun i hi => ?_)
    have h0 := hP i (Finset.mem_insert_of_mem hi)
    rw [hP', map_mul, phi_lf] at h0
    exact (mul_eq_zero.1 h0).resolve_left
      (lf_ne_zero (hd i a (fun h => ha (h ▸ hi))))

theorem deg_prod (t : Fin 91 → Triple) (ht : ∀ i, t i ≠ 0) (S : Finset (Fin 91)) :
    (∏ i ∈ S, lf (t i)) ≠ 0 ∧ S.card ≤ (∏ i ∈ S, lf (t i)).totalDegree := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := lf_ne_zero (ht a)
    refine ⟨mul_ne_zero h1 ih.1, ?_⟩
    rw [totalDegree_mul_of_isDomain h1 ih.1]
    have := one_le_deg_lf (ht a)
    omega

/-! ### On the plane, `A(Z)` is a multiple of `x` -/

theorem par_vec {K : Type*} [CommRing K] (P Q x e : Fin 3 → K)
    (hP : x 0 * P 0 + x 1 * P 1 + x 2 * P 2 = 0) (hQ : x 0 * Q 0 + x 1 * Q 1 + x 2 * Q 2 = 0)
    (he : x 0 * e 0 + x 1 * e 1 + x 2 * e 2 = 1) (A : Fin 3 → K)
    (hA : A = ![P 1 * Q 2 - P 2 * Q 1, P 2 * Q 0 - P 0 * Q 2, P 0 * Q 1 - P 1 * Q 0]) (k : Fin 3) :
    A k = (e 0 * A 0 + e 1 * A 1 + e 2 * A 2) * x k := by
  subst hA
  fin_cases k <;> simp
  · linear_combination (-(P 1 * Q 2 - P 2 * Q 1)) * he + (-(e 1 * P 2) + e 2 * P 1) * hQ
      + (e 1 * Q 2 - e 2 * Q 1) * hP
  · linear_combination (-(P 2 * Q 0 - P 0 * Q 2)) * he + (-(e 2 * P 0) + e 0 * P 2) * hQ
      + (e 2 * Q 0 - e 0 * Q 2) * hP
  · linear_combination (-(P 0 * Q 1 - P 1 * Q 0)) * he + (-(e 0 * P 1) + e 1 * P 0) * hQ
      + (e 0 * Q 1 - e 1 * Q 0) * hP

/-- Cubing the variables. -/
noncomputable def psi : R →ₐ[F9] R := bind₁ (fun j => X j ^ 3)

/-- `w_i = Z_i − e_i³ (x^(3) · Z)`, so that `ψ w_i = (φ Z_i)³`. -/
noncomputable def wv (x e : Triple) (i : Fin 3) : R :=
  X i - MvPolynomial.C (e i ^ 3) * lf (cube3 x)

/-- `G(Z) = h(x, w(Z))`. -/
noncomputable def Gpoly (c : Mon → F9) (x e : Triple) : R :=
  ∑ m : Mon, MvPolynomial.C (c m * mon m.val.1 x) * pmon m.val.2 (wv x e)

theorem alg_C (f : R →ₐ[F9] R) (a : F9) : f (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [algHom_C]; rfl

theorem psi_lf (v : Triple) : psi (lf v) = lfp v 3 := by
  simp only [psi, lf, lfp, map_add, map_mul, bind₁_X_right, bind₁_C_right]

theorem psi_wv (x e : Triple) (i : Fin 3) : psi (wv x e i) = gv x e i ^ 3 := by
  rw [gv, cube_sub2 h3R, mul_pow, lf_cube, wv, map_sub, map_mul, psi_lf, alg_C, map_pow]
  simp only [psi, bind₁_X_right]

theorem nine_sub {K : Type*} [CommRing K] (h3 : (3 : K) = 0) (a b : K) :
    (a - b) ^ 9 = a ^ 9 - b ^ 9 := by
  rw [show 9 = 3 * 3 from rfl, pow_mul, cube_sub2 h3, cube_sub2 h3, ← pow_mul, ← pow_mul]

theorem gv_nine (x e : Triple) (i : Fin 3) :
    gv x e i ^ 9 = X i ^ 9 - MvPolynomial.C (e i) * lfp x 9 := by
  rw [gv, nine_sub h3R, mul_pow, lf_nine, ← map_pow, pow_nine]

theorem pmon_smul (a : E3) (ha : tot a = 4) (l : R) (x : Triple) :
    pmon a (fun k => l * MvPolynomial.C (x k)) = l ^ 4 * MvPolynomial.C (mon a x) := by
  simp only [pmon, mon, mul_pow, map_mul, map_pow]
  rw [← ha]; unfold tot; ring

theorem pmon_psi (b : E3) (w : Fin 3 → R) : pmon b (fun k => psi (w k)) = psi (pmon b w) := by
  simp only [pmon, map_mul, map_pow]

theorem phi_Q (c : Mon → F9) (x e : Triple) (he : dot x e = 1) :
    phi x e (Qpoly c) = (∑ k, MvPolynomial.C (e k) * phi x e (Acoord k)) ^ 4 *
      psi (Gpoly c x e) := by
  set lam := ∑ k, MvPolynomial.C (e k) * phi x e (Acoord k) with hlam
  have heC : MvPolynomial.C (x 0) * MvPolynomial.C (e 0) + MvPolynomial.C (x 1) * MvPolynomial.C (e 1)
      + MvPolynomial.C (x 2) * MvPolynomial.C (e 2) = (1 : R) := by
    have := congrArg (MvPolynomial.C : F9 → R) he
    simpa [dot, Fin.sum_univ_three, map_add, map_mul] using this
  have hP : MvPolynomial.C (x 0) * gv x e 0 + MvPolynomial.C (x 1) * gv x e 1
      + MvPolynomial.C (x 2) * gv x e 2 = 0 := by
    simp only [gv, lf]
    linear_combination (-(MvPolynomial.C (x 0) * X 0 + MvPolynomial.C (x 1) * X 1
      + MvPolynomial.C (x 2) * X 2)) * heC
  have hQ : MvPolynomial.C (x 0) * gv x e 0 ^ 9 + MvPolynomial.C (x 1) * gv x e 1 ^ 9
      + MvPolynomial.C (x 2) * gv x e 2 ^ 9 = 0 := by
    simp only [gv_nine, lfp]
    linear_combination (-(MvPolynomial.C (x 0) * X 0 ^ 9 + MvPolynomial.C (x 1) * X 1 ^ 9
      + MvPolynomial.C (x 2) * X 2 ^ 9)) * heC
  have hA : ∀ k, phi x e (Acoord k) = lam * MvPolynomial.C (x k) := by
    intro k
    have key := par_vec (gv x e) (fun k => gv x e k ^ 9) (fun k => MvPolynomial.C (x k))
      (fun k => MvPolynomial.C (e k)) hP hQ heC (fun k => phi x e (Acoord k))
      (by
        funext k
        fin_cases k <;> simp [Acoord, phi, bind₁_X_right]) k
    rw [key, hlam, Fin.sum_univ_three]
  have hterm : ∀ m : Mon, phi x e (MvPolynomial.C (c m) * pmon m.val.1 Acoord *
      pmon m.val.2 (fun k => X k ^ 3))
      = lam ^ 4 * psi (MvPolynomial.C (c m * mon m.val.1 x) * pmon m.val.2 (wv x e)) := by
    intro m
    have e1 : phi x e (pmon m.val.1 Acoord) =
        pmon m.val.1 (fun k => lam * MvPolynomial.C (x k)) := by
      simp only [pmon, map_mul, map_pow, hA]
    have e2 : phi x e (pmon m.val.2 (fun k => X k ^ 3)) = psi (pmon m.val.2 (wv x e)) := by
      rw [← pmon_psi]
      simp only [pmon, map_mul, map_pow, psi_wv]
      simp only [phi, bind₁_X_right]
    rw [map_mul, map_mul, e1, e2, pmon_smul _ m.2.1, alg_C, map_mul, alg_C, map_mul]
    ring
  simp only [Qpoly, map_sum, hterm, Gpoly, ← Finset.mul_sum]

/-! ### `G` vanishes: degree at most four, zero on all of `F9³` -/

theorem card_F9 : Fintype.card F9 = 9 := by rfl

theorem pmon_deg (b : E3) (P : Fin 3 → R) (d : ℕ) (hP : ∀ k, (P k).totalDegree ≤ d) :
    (pmon b P).totalDegree ≤ d * tot b := by
  unfold pmon tot
  calc (P 0 ^ (b 0 : ℕ) * P 1 ^ (b 1 : ℕ) * P 2 ^ (b 2 : ℕ)).totalDegree
      ≤ (P 0 ^ (b 0 : ℕ)).totalDegree + (P 1 ^ (b 1 : ℕ)).totalDegree
        + (P 2 ^ (b 2 : ℕ)).totalDegree := by
        refine (totalDegree_mul _ _).trans ?_
        gcongr
        exact totalDegree_mul _ _
    _ ≤ (b 0 : ℕ) * d + (b 1 : ℕ) * d + (b 2 : ℕ) * d := by
        gcongr <;>
        exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hP _))
    _ = d * ((b 0 : ℕ) + (b 1 : ℕ) + (b 2 : ℕ)) := by ring

theorem deg_CX (a : F9) (i : Fin 3) (n : ℕ) : (MvPolynomial.C a * X i ^ n : R).totalDegree ≤ n :=
  (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X_pow])

theorem deg_lf (v : Triple) : (lf v).totalDegree ≤ 1 := by
  unfold lf
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le ?_ ?_)) ?_) <;>
  simpa using deg_CX _ _ 1

theorem deg_wv (x e : Triple) (i : Fin 3) : (wv x e i).totalDegree ≤ 1 := by
  unfold wv
  refine (totalDegree_sub _ _).trans (max_le (by simp [totalDegree_X]) ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]; exact deg_lf _

theorem deg_G (c : Mon → F9) (x e : Triple) : (Gpoly c x e).totalDegree ≤ 4 := by
  unfold Gpoly
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  have := pmon_deg m.val.2 (wv x e) 1 (deg_wv x e)
  rw [m.2.2.1] at this
  rw [totalDegree_C, zero_add]; simpa using this

theorem eval_G (c : Mon → F9) (x e z : Triple) :
    eval z (Gpoly c x e) = hval c x (fun k => z k - e k ^ 3 * dot (cube3 x) z) := by
  simp only [Gpoly, hval, map_sum, map_mul, eval_C, pmon, mon, map_pow, wv, map_sub, lf,
    map_add, eval_X, dot, Fin.sum_univ_three, cube3]

theorem G_zero (c : Mon → F9) (x e : Triple) (he : dot x e = 1)
    (hh : ∀ y, dot (cube3 x) y = 0 → hval c x y = 0) : Gpoly c x e = 0 := by
  apply eq_zero_of_eval_zero_at_prod_finset _ (fun _ => Finset.univ)
  · intro i
    rw [Finset.card_univ, card_F9]
    have := (degreeOf_le_totalDegree _ i).trans (deg_G c x e)
    omega
  · intro z _
    rw [eval_G]
    apply hh
    have h1 : x 0 ^ 3 * e 0 ^ 3 + x 1 ^ 3 * e 1 ^ 3 + x 2 ^ 3 * e 2 ^ 3 = 1 := by
      have := congrArg (· ^ 3) he
      simp only [dot, Fin.sum_univ_three, cube_add3 h3F, mul_pow, one_pow] at this
      exact this
    simp only [dot, Fin.sum_univ_three, cube3]
    linear_combination (-(x 0 ^ 3 * z 0 + x 1 ^ 3 * z 1 + x 2 ^ 3 * z 2)) * h1

/-! ### From the hypothesis to whole planes -/

theorem nrm_surj0 : ∀ a : F9, ∃ j : Fin 91, triple j = ![0, 1, a] := by decide +kernel

theorem nrm_surj1 : ∀ a b : F9, ∃ j : Fin 91, triple j = ![1, a, b] := by decide +kernel

theorem nrm_surj (u : Triple) (hu : Nrm u) : ∃ j, triple j = u := by
  have hu' : u = ![u 0, u 1, u 2] := by funext k; fin_cases k <;> rfl
  rcases hu with ⟨h0, h1, h2⟩ | ⟨h0, h1⟩ | h0
  · refine ⟨0, ?_⟩
    rw [hu', h0, h1, h2]; decide
  · obtain ⟨j, hj⟩ := nrm_surj0 (u 2)
    exact ⟨j, by rw [hj, hu', h0, h1]; rfl⟩
  · obtain ⟨j, hj⟩ := nrm_surj1 (u 1) (u 2)
    exact ⟨j, by rw [hj, hu', h0]; rfl⟩

theorem nrm_cube {u : Triple} (hu : Nrm u) : Nrm (cube3 u) := by
  unfold Nrm cube3
  rcases hu with ⟨h0, h1, h2⟩ | ⟨h0, h1⟩ | h0
  · simp [h0, h1, h2]
  · simp [h0, h1]
  · simp [h0]

theorem nz_norm (y : Triple) (hy : y ≠ 0) : ∃ j : Fin 91, ∃ d : F9, d ≠ 0 ∧ y = d • triple j := by
  have key : ∀ d : F9, d ≠ 0 → Nrm (d⁻¹ • y) → ∃ j : Fin 91, ∃ d : F9, d ≠ 0 ∧ y = d • triple j := by
    intro d hd hn
    obtain ⟨j, hj⟩ := nrm_surj _ hn
    exact ⟨j, d, hd, by rw [hj, smul_smul, mul_inv_cancel₀ hd, one_smul]⟩
  by_cases h0 : y 0 = 0
  · by_cases h1 : y 1 = 0
    · have h2 : y 2 ≠ 0 := by
        intro h2; apply hy; funext k; fin_cases k <;> simp [h0, h1, h2]
      exact key (y 2) h2 (Or.inl ⟨by simp [h0], by simp [h1], by simp [h2]⟩)
    · exact key (y 1) h1 (Or.inr (Or.inl ⟨by simp [h0], by simp [h1]⟩))
  · exact key (y 0) h0 (Or.inr (Or.inr (by simp [h0])))

theorem hval_smul (c : Mon → F9) (x : Triple) (d : F9) (y : Triple) :
    hval c x (d • y) = d ^ 4 * hval c x y := by
  simp only [hval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hb : tot m.val.2 = 4 := m.2.2.1
  simp only [mon, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← hb]; unfold tot; ring

theorem dot_smul (u y : Triple) (d : F9) : dot u (d • y) = d * dot u y := by
  simp only [dot, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]; ring

theorem hval_plane (c : Mon → F9)
    (h : ∀ i j : Fin 91, dot (triple i) (triple j) = 0 → hval c (cube3 (triple i)) (triple j) = 0)
    (i : Fin 91) (y : Triple) (hy : dot (cube3 (triple i)) y = 0) : hval c (triple i) y = 0 := by
  obtain ⟨i', hi'⟩ := nrm_surj _ (nrm_cube (nrm_triple i))
  by_cases y0 : y = 0
  · rw [y0, show (0 : Triple) = (0 : F9) • triple 0 by simp, hval_smul]; simp
  obtain ⟨j, d, hd, rfl⟩ := nz_norm y y0
  rw [hval_smul]
  have hdot : dot (triple i') (triple j) = 0 := by
    rw [dot_smul] at hy
    rw [hi']; exact (mul_eq_zero.1 hy).resolve_left hd
  have := h i' j hdot
  rw [hi', cube_cube] at this
  rw [this, mul_zero]

theorem e_exists (i : Fin 91) : ∃ e : Triple, dot (triple i) e = 1 := by
  rcases nrm_triple i with ⟨-, -, h2⟩ | ⟨-, h1⟩ | h0
  · exact ⟨![0, 0, 1], by simp [dot, Fin.sum_univ_three, h2]⟩
  · exact ⟨![0, 1, 0], by simp [dot, Fin.sum_univ_three, h1]⟩
  · exact ⟨![1, 0, 0], by simp [dot, Fin.sum_univ_three, h0]⟩

theorem distinct (e : Fin 91 → Triple) (i j : Fin 91) (hij : i ≠ j) :
    (fun k => triple j k - dot (triple j) (e i) * triple i k) ≠ 0 := by
  intro h
  have hj : triple j = dot (triple j) (e i) • triple i := by
    funext k
    have := congrFun h k
    simp only [Pi.zero_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination this
  have hc : triple j ⨯₃ triple i = 0 := by
    rw [hj, LinearMap.map_smul₂, cross_self, smul_zero]
  exact hij (triple_inj (cross_zero_eq (nrm_triple j) (nrm_triple i) hc)).symm

theorem triple_ne_zero' (i : Fin 91) : triple i ≠ 0 := by
  intro h
  rcases nrm_triple i with ⟨-, -, h2⟩ | ⟨-, h1⟩ | h0
  · rw [h] at h2; exact zero_ne_one h2
  · rw [h] at h1; exact zero_ne_one h1
  · rw [h] at h0; exact zero_ne_one h0

/-! ### The degree of `Q_h` -/

theorem deg_A (k : Fin 3) : (Acoord k).totalDegree ≤ 10 := by
  have hm : ∀ i j : Fin 3, (X i * X j ^ 9 : R).totalDegree ≤ 10 := fun i j =>
    (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_X_pow])
  fin_cases k <;>
  · simp only [Acoord]
    exact (totalDegree_sub _ _).trans (max_le (hm _ _) (hm _ _))

theorem deg_Q (c : Mon → F9) : (Qpoly c).totalDegree ≤ 52 := by
  unfold Qpoly
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  have h1 := pmon_deg m.val.1 Acoord 10 deg_A
  have h2 := pmon_deg m.val.2 (fun k => X k ^ 3) 3 (fun k => by simp [totalDegree_X_pow])
  rw [m.2.1] at h1
  rw [m.2.2.1] at h2
  refine (totalDegree_mul _ _).trans ?_
  have h3 := (totalDegree_mul (MvPolynomial.C (c m)) (pmon m.val.1 Acoord)).trans
    (add_le_add (le_of_eq (totalDegree_C (c m))) h1)
  omega

end MultipleUnicast.Counterexample.Dev.DimVanish

namespace MultipleUnicast.Counterexample.Dev.Dim
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.DimVanish MvPolynomial

/-- Paper (2) ⇒ (5): if `h(p^(3), ℓ) = 0` at every incident pair of normalized triples, then
`Q_h = 0` as a polynomial. -/
theorem core_vanish (c : Mon → F9)
    (h : ∀ i j : Fin 91, dot (triple i) (triple j) = 0 → hval c (cube3 (triple i)) (triple j) = 0) :
    Qpoly c = 0 := by
  choose e he using e_exists
  have hP : ∀ i, phi (triple i) (e i) (Qpoly c) = 0 := by
    intro i
    rw [phi_Q c _ _ (he i), G_zero c _ _ (he i) (hval_plane c h i), map_zero, mul_zero]
  by_contra hQ
  have hdvd := peel triple e (distinct e) Finset.univ (Qpoly c) (fun i _ => hP i)
  have h1 := totalDegree_le_of_dvd_of_isDomain hdvd hQ
  have h2 := (deg_prod triple triple_ne_zero' Finset.univ).2
  have h3 := deg_Q c
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

end MultipleUnicast.Counterexample.Dev.Dim
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false
open scoped Classical

/-! Paper, Appendix B, "Distinct leading terms force independence": in the lexicographic order
with `Z₀` first, `A(Z)^a (Z^(3))^b` has leading exponent
`(9(a₁+a₂)+3b₀, 9a₀+a₂+3b₁, a₀+a₁+3b₂)`, and these are pairwise distinct over the retained
monomials, so `Q_h = 0` forces `h = 0`. -/

namespace MultipleUnicast.Counterexample.Dev.DimLead
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Dim MvPolynomial

abbrev P3 := MvPolynomial (Fin 3) F9

/-- The lexicographic monomial order on `Fin 3`, `Z₀` most significant. -/
noncomputable abbrev ord : MonomialOrder (Fin 3) := MonomialOrder.lex

theorem lex_lt_of (c d : Fin 3 →₀ ℕ)
    (h : c 0 < d 0 ∨ (c 0 = d 0 ∧ (c 1 < d 1 ∨ (c 1 = d 1 ∧ c 2 < d 2)))) :
    ord.toSyn c < ord.toSyn d := by
  show toLex c < toLex d
  rw [Finsupp.Lex.lt_iff]
  rcases h with h | ⟨h0, h | ⟨h1, h2⟩⟩
  · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩
  · refine ⟨1, fun j hj => ?_, h⟩
    fin_cases j
    · exact h0
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
  · refine ⟨2, fun j hj => ?_, h2⟩
    fin_cases j
    · exact h0
    · exact h1
    · exact absurd hj (by decide)

theorem deg_XX (s t : Fin 3) (k : ℕ) :
    ord.degree (X s * X t ^ k : P3) = Finsupp.single s 1 + k • Finsupp.single t 1 := by
  rw [MonomialOrder.degree_mul (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)),
    MonomialOrder.degree_pow, MonomialOrder.degree_X, MonomialOrder.degree_X]

theorem deg_sub_left (f g : P3) (h : ord.toSyn (ord.degree g) < ord.toSyn (ord.degree f)) :
    ord.degree (f - g) = ord.degree f ∧ f - g ≠ 0 := by
  refine ⟨MonomialOrder.degree_sub_of_lt h, fun e => ?_⟩
  rw [sub_eq_zero] at e
  rw [e] at h
  exact lt_irrefl _ h

theorem deg_sub_right (f g : P3) (h : ord.toSyn (ord.degree f) < ord.toSyn (ord.degree g)) :
    ord.degree (f - g) = ord.degree g ∧ f - g ≠ 0 := by
  have := deg_sub_left g f h
  rw [← neg_sub, MonomialOrder.degree_neg, neg_ne_zero]
  exact this

/-- Leading exponents of `A₀, A₁, A₂`. -/
noncomputable def dA : Fin 3 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 2 1 + 9 • Finsupp.single 1 1, Finsupp.single 2 1 + 9 • Finsupp.single 0 1,
    Finsupp.single 1 1 + 9 • Finsupp.single 0 1]

theorem A_spec (k : Fin 3) : ord.degree (Acoord k) = dA k ∧ Acoord k ≠ 0 := by
  fin_cases k
  · have e : Acoord 0 = X 1 * X 2 ^ 9 - X 2 * X 1 ^ 9 := rfl
    show ord.degree (Acoord 0) = dA 0 ∧ Acoord 0 ≠ 0
    rw [e]
    have := deg_sub_right (X 1 * X 2 ^ 9 : P3) (X 2 * X 1 ^ 9) (by
      rw [deg_XX, deg_XX]; apply lex_lt_of; simp)
    rw [this.1, deg_XX]
    exact ⟨rfl, this.2⟩
  · have e : Acoord 1 = X 2 * X 0 ^ 9 - X 0 * X 2 ^ 9 := rfl
    show ord.degree (Acoord 1) = dA 1 ∧ Acoord 1 ≠ 0
    rw [e]
    have := deg_sub_left (X 2 * X 0 ^ 9 : P3) (X 0 * X 2 ^ 9) (by
      rw [deg_XX, deg_XX]; apply lex_lt_of; simp)
    rw [this.1, deg_XX]
    exact ⟨rfl, this.2⟩
  · have e : Acoord 2 = X 0 * X 1 ^ 9 - X 1 * X 0 ^ 9 := rfl
    show ord.degree (Acoord 2) = dA 2 ∧ Acoord 2 ≠ 0
    rw [e]
    have := deg_sub_right (X 0 * X 1 ^ 9 : P3) (X 1 * X 0 ^ 9) (by
      rw [deg_XX, deg_XX]; apply lex_lt_of; simp)
    rw [this.1, deg_XX]
    exact ⟨rfl, this.2⟩

theorem X3_spec (k : Fin 3) :
    ord.degree ((fun k => X k ^ 3 : Fin 3 → P3) k) = 3 • Finsupp.single k 1 ∧
      (fun k => X k ^ 3 : Fin 3 → P3) k ≠ 0 :=
  ⟨by simp only [MonomialOrder.degree_pow, MonomialOrder.degree_X], pow_ne_zero _ (X_ne_zero _)⟩

theorem pmon_spec (a : E3) (P : Fin 3 → P3) (d : Fin 3 → (Fin 3 →₀ ℕ))
    (h : ∀ k, ord.degree (P k) = d k ∧ P k ≠ 0) :
    ord.degree (pmon a P) = (a 0 : ℕ) • d 0 + (a 1 : ℕ) • d 1 + (a 2 : ℕ) • d 2 ∧ pmon a P ≠ 0 := by
  have n0 := pow_ne_zero (a 0 : ℕ) (h 0).2
  have n1 := pow_ne_zero (a 1 : ℕ) (h 1).2
  have n2 := pow_ne_zero (a 2 : ℕ) (h 2).2
  unfold pmon
  refine ⟨?_, mul_ne_zero (mul_ne_zero n0 n1) n2⟩
  rw [MonomialOrder.degree_mul (mul_ne_zero n0 n1) n2, MonomialOrder.degree_mul n0 n1,
    MonomialOrder.degree_pow, MonomialOrder.degree_pow, MonomialOrder.degree_pow,
    (h 0).1, (h 1).1, (h 2).1]

/-- The polynomial `A(Z)^a (Z^(3))^b` of a retained monomial. -/
noncomputable def P (m : Mon) : P3 := pmon m.val.1 Acoord * pmon m.val.2 (fun k => X k ^ 3)

/-- Its leading exponent. -/
noncomputable def D (m : Mon) : Fin 3 →₀ ℕ :=
  ((m.val.1 0 : ℕ) • dA 0 + (m.val.1 1 : ℕ) • dA 1 + (m.val.1 2 : ℕ) • dA 2) +
    ((m.val.2 0 : ℕ) • (3 • Finsupp.single 0 1) + (m.val.2 1 : ℕ) • (3 • Finsupp.single 1 1) +
      (m.val.2 2 : ℕ) • (3 • Finsupp.single 2 1))

theorem P_spec (m : Mon) : ord.degree (P m) = D m ∧ P m ≠ 0 := by
  have h1 := pmon_spec m.val.1 Acoord dA A_spec
  have h2 := pmon_spec m.val.2 (fun k => X k ^ 3) (fun k => 3 • Finsupp.single k 1) X3_spec
  unfold P
  exact ⟨by rw [MonomialOrder.degree_mul h1.2 h2.2, h1.1, h2.1]; rfl, mul_ne_zero h1.2 h2.2⟩

theorem D_inj {m m' : Mon} (h : D m = D m') : m = m' := by
  have e0 := congrArg (fun d => d 0) h
  have e1 := congrArg (fun d => d 1) h
  have e2 := congrArg (fun d => d 2) h
  simp [D, dA] at e0 e1 e2
  obtain ⟨⟨a, b⟩, hr⟩ := m
  obtain ⟨⟨a', b'⟩, hr'⟩ := m'
  simp only [retained, tot] at hr hr' e0 e1 e2
  have q0 : (a 0 : ℕ) = a' 0 ∧ (a 1 : ℕ) = a' 1 ∧ (a 2 : ℕ) = a' 2 ∧
      (b 0 : ℕ) = b' 0 ∧ (b 1 : ℕ) = b' 1 ∧ (b 2 : ℕ) = b' 2 := by
    have s0 : (b 0 : ℕ) + 3 * a' 0 = b' 0 + 3 * a 0 := by omega
    have s1 : (a 0 : ℕ) = a' 0 := by omega
    have s2 : (a' 1 : ℕ) + 3 * b 1 = a 1 + 3 * b' 1 := by omega
    have s3 : (b 1 : ℕ) = b' 1 := by omega
    omega
  apply Subtype.ext
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    exact Fin.ext (by simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; omega)

theorem lead (c : Mon → F9) (h : Qpoly c = 0) : c = 0 := by
  by_contra hc
  have hS : (Finset.univ.filter fun m => c m ≠ 0).Nonempty := by
    obtain ⟨m, hm⟩ := Function.ne_iff.1 hc
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image _ (fun m => ord.toSyn (D m)) hS
  have hq : (Qpoly c).coeff (D m0) = c m0 * (P m0).coeff (D m0) := by
    unfold Qpoly
    rw [coeff_sum, Finset.sum_eq_single m0]
    · rw [mul_assoc, coeff_C_mul]
      rfl
    · intro m _ hne
      by_cases hcm : c m = 0
      · simp [hcm]
      · rw [mul_assoc, coeff_C_mul]
        have : (P m).coeff (D m0) = 0 := by
          apply MonomialOrder.coeff_eq_zero_of_lt
          rw [(P_spec m).1]
          exact lt_of_le_of_ne (hmax m (by simpa using hcm))
            (fun e => hne (D_inj (ord.toSyn.injective e)))
        exact (congrArg (c m * ·) this).trans (mul_zero _)
    · simp
  rw [h, coeff_zero] at hq
  have hne : (P m0).coeff (D m0) ≠ 0 := by
    rw [← (P_spec m0).1]
    exact MonomialOrder.coeff_degree_ne_zero_iff.2 (P_spec m0).2
  exact (mul_ne_zero (by simpa using hm0) hne) hq.symm

end MultipleUnicast.Counterexample.Dev.DimLead

namespace MultipleUnicast.Counterexample.Dev.Dim
open MultipleUnicast.Counterexample MvPolynomial

/-- Paper, "Distinct leading terms force independence": `Q_h = 0` forces every coefficient to vanish. -/
theorem core_lead (c : Mon → F9) (h : Qpoly c = 0) : c = 0 :=
  DimLead.lead c h

end MultipleUnicast.Counterexample.Dev.Dim
end

section
set_option autoImplicit false

namespace MultipleUnicast.Counterexample.Dev.Dim
open MultipleUnicast.Counterexample

theorem core (c : Mon → F9)
    (h : ∀ i j : Fin 91, dot (triple i) (triple j) = 0 → hval c (cube3 (triple i)) (triple j) = 0) :
    c = 0 :=
  core_lead c (core_vanish c h)

end MultipleUnicast.Counterexample.Dev.Dim
end

section
set_option maxRecDepth 2048
set_option autoImplicit false
set_option Elab.async false
open scoped Classical

/-! The dimension bound (paper, Appendix B): the 166 vectors `w_m` lie in `W` and are linearly
independent, by `Dev.Dim.core`. -/

namespace MultipleUnicast.Counterexample.Dev.DimMain
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Dim
  MultipleUnicast.Counterexample.Dev.RILocal MultipleUnicast.Counterexample.Dev.TermDist

/-! ### Products of four binary linear forms -/

/-- Coefficients of `∏_j (x u_j + y w_j)` as a binary quartic. -/
def qc (u w : Fin 4 → F9) : Fin 5 → F9 :=
  ![u 0 * u 1 * u 2 * u 3,
    w 0 * u 1 * u 2 * u 3 + u 0 * w 1 * u 2 * u 3 + u 0 * u 1 * w 2 * u 3 + u 0 * u 1 * u 2 * w 3,
    w 0 * w 1 * u 2 * u 3 + w 0 * u 1 * w 2 * u 3 + w 0 * u 1 * u 2 * w 3 + u 0 * w 1 * w 2 * u 3 +
      u 0 * w 1 * u 2 * w 3 + u 0 * u 1 * w 2 * w 3,
    u 0 * w 1 * w 2 * w 3 + w 0 * u 1 * w 2 * w 3 + w 0 * w 1 * u 2 * w 3 + w 0 * w 1 * w 2 * u 3,
    w 0 * w 1 * w 2 * w 3]

theorem qc_spec (u w : Fin 4 → F9) (x y : F9) :
    (x * u 0 + y * w 0) * (x * u 1 + y * w 1) * (x * u 2 + y * w 2) * (x * u 3 + y * w 3) =
      ∑ r : Fin 5, qc u w r * (x ^ (4 - r.val) * y ^ r.val) := by
  simp only [Fin.sum_univ_five, qc]
  simp
  ring

/-- The `j`-th variable in the expansion of the monomial `z^e` as a product of four variables. -/
def idx (e : E3) (j : Fin 4) : Fin 3 :=
  if j.val < (e 0 : ℕ) then 0 else if j.val < (e 0 : ℕ) + (e 1 : ℕ) then 1 else 2

theorem mon_four (e : E3) (he : tot e = 4) (z : Triple) :
    mon e z = z (idx e 0) * z (idx e 1) * z (idx e 2) * z (idx e 3) := by
  unfold mon idx
  unfold tot at he
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  generalize (e 0 : ℕ) = n0 at *
  generalize (e 1 : ℕ) = n1 at *
  generalize (e 2 : ℕ) = n2 at *
  obtain rfl : n2 = 4 - n0 - n1 := by omega
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  interval_cases n0 <;> interval_cases n1 <;> first | omega |
    (simp only [v0, v1, v2, v3, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte]; ring)

theorem mon_lin (e : E3) (he : tot e = 4) (U W : Triple) (x y : F9) :
    mon e (x • U + y • W) =
      ∑ r : Fin 5, qc (fun j => U (idx e j)) (fun j => W (idx e j)) r * (x ^ (4 - r.val) * y ^ r.val) := by
  rw [mon_four e he, ← qc_spec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem add_cube (a b : F9) : (a + b) ^ 3 = a ^ 3 + b ^ 3 := by
  linear_combination (a ^ 2 * b + a * b ^ 2) * three_eq_zero

theorem cube3_lin (U W : Triple) (x y : F9) :
    cube3 (x • U + y • W) = x ^ 3 • cube3 U + y ^ 3 • cube3 W := by
  funext k
  simp only [cube3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_cube, mul_pow]

/-! ### The vectors `w_m` lie in `W` -/

theorem wvec_mem (m : Mon) : wvec m ∈ W := by
  simp only [W, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_range]
  intro v
  by_cases hv : v.val < 91
  · refine ⟨fun r => mon m.val.1 (cube3 (triple (vertexTriple v))) *
      qc (fun j => basisU v (idx m.val.2 j)) (fun j => basisW v (idx m.val.2 j)) r, ?_⟩
    funext q
    simp only [localEvaluation, incidentValues, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with hq
    · have hep := ep_eq hq
      rw [if_pos hv] at hep
      have hc := coord_spec hq
      rw [neighborOn_eq] at hc
      simp only [wvec, hep, hc, mon_lin _ m.2.2.1, localWeight, if_pos hv, Finset.mul_sum, mul_assoc]
    · rfl
  · refine ⟨fun r => mon m.val.2 (triple (vertexTriple v)) *
      qc (fun j => cube3 (basisU v) (idx m.val.1 j)) (fun j => cube3 (basisW v) (idx m.val.1 j)) r, ?_⟩
    funext q
    simp only [localEvaluation, incidentValues, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with hq
    · have hep := ep_eq hq
      rw [if_neg hv] at hep
      have hc := coord_spec hq
      rw [neighborOn_eq] at hc
      simp only [wvec, hep, hc, cube3_lin, mon_lin _ m.2.1, localWeight, if_neg hv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    · rfl

/-! ### Linear independence -/

theorem exists_edge (i j : Fin 91) (h : dot (triple i) (triple j) = 0) :
    ∃ q : Edge, edgePair q = (i, j) := by
  have hm : (i, j) ∈ incidenceList := by simp [incidenceList, h]
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.1 hm
  have hl := balanced_orientation.1
  refine ⟨⟨n, hl ▸ hn⟩, ?_⟩
  unfold edgePair
  rw [List.getD_eq_getElem _ _ hn]
  exact hget

theorem wvec_li : LinearIndependent F9 wvec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hz := core g (fun i j hij => by
    obtain ⟨q, hq⟩ := exists_edge i j hij
    have := congrFun hg q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, wvec, hq] at this
    simpa [hval, mul_assoc] using this)
  intro m
  rw [hz]
  rfl

/-! ### At least 166 retained monomials -/

/-- The retained monomials, encoded in base 5 as `a₀ + 5a₁ + 25a₂ + 125b₀ + 625b₁ + 3125b₂`. -/
def codes : List ℕ := [520, 540, 560, 580, 600, 1060, 1080, 1100, 1504, 1508, 1512, 1528, 1532, 1536, 1552, 1556, 1560, 1576, 1580, 1600, 2004, 2008, 2012, 2028, 2032, 2036, 2052, 2056, 2060, 2076, 2080, 2100, 2504, 2508, 2512, 2528, 2532, 2536, 2552, 2556, 2560, 2576, 2580, 2600, 3520, 3540, 3560, 3580, 3600, 4004, 4008, 4012, 4028, 4032, 4036, 4052, 4056, 4060, 4076, 4080, 4100, 4504, 4508, 4512, 4528, 4532, 4536, 4552, 4556, 4560, 4576, 4580, 4600, 5004, 5008, 5012, 5028, 5032, 5036, 5052, 5056, 5060, 5076, 5080, 5100, 6504, 6508, 6512, 6516, 6520, 6528, 6532, 6536, 6540, 6552, 6556, 6560, 6576, 6580, 6600, 7004, 7008, 7012, 7028, 7032, 7036, 7052, 7056, 7060, 7076, 7080, 7100, 7504, 7508, 7512, 7528, 7532, 7536, 7552, 7556, 7560, 7576, 7580, 7600, 9504, 9508, 9512, 9516, 9520, 9528, 9532, 9536, 9540, 9552, 9556, 9560, 9576, 9580, 9600, 10004, 10008, 10012, 10028, 10032, 10036, 10052, 10056, 10060, 10076, 10080, 10100, 12504, 12508, 12512, 12516, 12520, 12528, 12532, 12536, 12540, 12552, 12556, 12560, 12576, 12580, 12600]

def decode (n : ℕ) : E3 × E3 :=
  (fun k => ⟨n / 5 ^ k.val % 5, Nat.mod_lt _ (by norm_num)⟩,
    fun k => ⟨n / 5 ^ (3 + k.val) % 5, Nat.mod_lt _ (by norm_num)⟩)

def enc (m : E3 × E3) : ℕ :=
  (m.1 0 : ℕ) + 5 * (m.1 1 : ℕ) + 25 * (m.1 2 : ℕ) + 125 * (m.2 0 : ℕ) + 625 * (m.2 1 : ℕ) +
    3125 * (m.2 2 : ℕ)

theorem enc_decode (n : ℕ) (h : n < 15625) : enc (decode n) = n := by
  simp only [enc, decode, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  omega

theorem codes_len : codes.length = 166 := rfl

theorem codes_ret : ∀ i : Fin 166, retained (decode (codes.getD i 0)) := by decide +kernel

theorem codes_lt : ∀ i : Fin 166, codes.getD i 0 < 15625 := by decide +kernel

theorem codes_nodup : codes.Nodup := by decide +kernel

def g (i : Fin 166) : Mon := ⟨decode (codes.getD i 0), codes_ret i⟩

theorem g_inj : Function.Injective g := by
  intro i j h
  have h1 := congrArg (fun m : Mon => enc m.val) h
  simp only [g, enc_decode _ (codes_lt _)] at h1
  rw [List.getD_eq_getElem _ _ (by rw [codes_len]; exact i.2),
    List.getD_eq_getElem _ _ (by rw [codes_len]; exact j.2)] at h1
  exact Fin.ext ((codes_nodup.getElem_inj_iff).1 h1)

theorem card_mon : 166 ≤ Fintype.card Mon := by
  simpa using Fintype.card_le_of_injective g g_inj

end MultipleUnicast.Counterexample.Dev.DimMain

namespace MultipleUnicast.Counterexample
open MultipleUnicast.Counterexample.Dev.Dim MultipleUnicast.Counterexample.Dev.DimMain

/-- Appendix B, Proposition (unnumbered), PDF 16 / printed 15. -/
theorem chk_dimension_bound : 166 ≤ Module.finrank F9 W := by
  let w' : Mon → W := fun m => ⟨wvec m, wvec_mem m⟩
  have hli : LinearIndependent F9 w' := LinearIndependent.of_comp W.subtype wvec_li
  have := hli.fintype_card_le_finrank
  exact card_mon.trans this

end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_dimension_bound := @MultipleUnicast.Counterexample.chk_dimension_bound
