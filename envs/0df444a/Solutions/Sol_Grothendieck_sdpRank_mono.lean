-- Prove2me | solution 1 for Grothendieck.sdpRank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T16:08:59.536324+00:00
-- url     : https://prove2.me/submissions/3c21cd7a-beda-41c6-88e2-542215505448

import Mathlib
import Definitions.Def_Grothendieck_Sdp

set_option autoImplicit false

/-!
# Leaf 6 infrastructure, part 1: bounds and candidate lemmas for `sdpRank` / `sdpInf`

The definitions `edgeSum`, `sdpRank`, `sdpInf`, `grothendieckConstant` are the published
ones (`Definitions.Def_Grothendieck_Sdp`).  Everything here is about the *supremum*
machinery: an explicit candidate family bounds `sdpRank`/`sdpInf` from below, and the
candidate sets are bounded above, so `le_csSup` applies.  These are the glue lemmas any
proof about `K(r,G)` needs.
-/

noncomputable section

open scoped BigOperators Real ENNReal

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

section EdgeBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `Sym2`-sum of the absolute values of a symmetric kernel; the crude upper bound for
`edgeSum` over unit families. -/
def edgeAbsSum (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v => |A u v|, fun u v => by simp only [hA u v]⟩ e

/-- `Sym2`-level absolute value bound: a symmetric kernel bounded pointwise by `c` gives a
`Sym2`-sum bounded by the `Sym2`-sum of `c`. -/
theorem abs_lift_le {F : V → V → ℝ} (hF : ∀ u v, F u v = F v u) {c : V → V → ℝ}
    (hc : ∀ u v, c u v = c v u) (h : ∀ u v, |F u v| ≤ c u v) (e : Sym2 V) :
    |Sym2.lift ⟨F, hF⟩ e| ≤ Sym2.lift ⟨c, hc⟩ e := by
  induction e using Sym2.inductionOn with
  | _ u v => simpa using h u v

/-- The edge sum is bounded by `edgeAbsSum`, for vectors of norm at most one. -/
theorem abs_edgeSum_le (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → E) (hf : ∀ v, ‖f v‖ ≤ 1) :
    |edgeSum G A hA f| ≤ edgeAbsSum G A hA := by
  classical
  have hterm : ∀ u v : V, |A u v * inner ℝ (f u) (f v)| ≤ |A u v| := by
    intro u v
    have h1 : |inner ℝ (f u) (f v)| ≤ 1 := by
      have h2 : |inner ℝ (f u) (f v)| ≤ ‖f u‖ * ‖f v‖ := abs_real_inner_le_norm _ _
      have h3 : ‖f u‖ * ‖f v‖ ≤ 1 * 1 :=
        mul_le_mul (hf u) (hf v) (norm_nonneg _) (by norm_num)
      linarith
    have h4 : |A u v * inner ℝ (f u) (f v)| = |A u v| * |inner ℝ (f u) (f v)| := abs_mul _ _
    rw [h4]
    nlinarith [abs_nonneg (A u v)]
  have hsym : ∀ u v : V,
      (fun u v => A u v * inner ℝ (f u) (f v)) u v =
        (fun u v => A u v * inner ℝ (f u) (f v)) v u := by
    intro u v
    simp only [hA u v, real_inner_comm]
  have habs : ∀ u v : V, (fun u v => |A u v|) u v = (fun u v => |A u v|) v u := by
    intro u v
    simp only [hA u v]
  have hstep : ∀ e : Sym2 V,
      |Sym2.lift ⟨fun u v => A u v * inner ℝ (f u) (f v), hsym⟩ e| ≤
        Sym2.lift ⟨fun u v => |A u v|, habs⟩ e :=
    fun e => abs_lift_le hsym habs hterm e
  unfold edgeSum
  rw [edgeAbsSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun e _ => hstep e

end EdgeBounds

section Candidates

/-- The candidate set defining `sdpInf` is bounded above. -/
theorem bddAbove_sdpInf (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) :
    BddAbove {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f} := by
  refine ⟨edgeAbsSum G A hA, ?_⟩
  rintro x ⟨f, hf, rfl⟩
  exact (le_abs_self _).trans
    (abs_edgeSum_le G A hA f fun v => le_of_eq (hf v))

/-- The candidate set defining `sdpRank` is bounded above. -/
theorem bddAbove_sdpRank (r : ℕ) (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) :
    BddAbove {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r), (∀ v, ‖f v‖ = 1) ∧
      x = edgeSum G A hA f} := by
  refine ⟨edgeAbsSum G A hA, ?_⟩
  rintro x ⟨f, hf, rfl⟩
  exact (le_abs_self _).trans
    (abs_edgeSum_le G A hA f fun v => le_of_eq (hf v))

/-- Any unit family of `L²` vectors gives a lower bound for `sdpInf`. -/
theorem edgeSum_le_sdpInf (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → L2) (hf : ∀ v, ‖f v‖ = 1) :
    edgeSum G A hA f ≤ sdpInf G A hA :=
  le_csSup (bddAbove_sdpInf G A hA) ⟨f, hf, rfl⟩

/-- Any unit family of vectors in `R^r` gives a lower bound for `sdpRank`. -/
theorem edgeSum_le_sdpRank (r : ℕ) (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) (f : V → EuclideanSpace ℝ (Fin r))
    (hf : ∀ v, ‖f v‖ = 1) :
    edgeSum G A hA f ≤ sdpRank r G A hA :=
  le_csSup (bddAbove_sdpRank r G A hA) ⟨f, hf, rfl⟩

end Candidates


section ConstKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constant-`1` kernel, with its canonical symmetry proof. -/
def oneKernel : V → V → ℝ := fun _ _ => 1

theorem oneKernel_symm : ∀ u v, oneKernel (V := V) u v = oneKernel v u := fun _ _ => rfl

/-- The `Sym2`-lift of the constant-`1` kernel is the constant `1`. -/
theorem lift_const_one (e : Sym2 V) :
    Sym2.lift ⟨fun _ _ : V => (1 : ℝ), fun _ _ => rfl⟩ e = 1 := by
  induction e using Sym2.inductionOn with
  | _ u v => simp

/-- The number of edges of `G`, as a real number. -/
def edgeCount (G : SimpleGraph V) : ℝ := by
  classical
  exact (G.edgeFinset.card : ℝ)

theorem edgeCount_nonneg (G : SimpleGraph V) : 0 ≤ edgeCount G := by
  rw [edgeCount]; positivity

/-- `edgeAbsSum` of the constant-`1` kernel is the number of edges. -/
theorem edgeAbsSum_oneKernel (G : SimpleGraph V) :
    edgeAbsSum G oneKernel oneKernel_symm = edgeCount G := by
  classical
  rw [edgeCount]
  unfold edgeAbsSum
  trans ∑ e ∈ G.edgeFinset, (1 : ℝ)
  · exact Finset.sum_congr rfl fun e _ => by
      induction e using Sym2.inductionOn with
      | _ u v => simp [oneKernel]
  · simp

/-- The edge sum of the constant-`1` kernel against a constant unit family is the number of
edges. -/
theorem edgeSum_oneKernel (G : SimpleGraph V) (f : V → E) (c : E) (hf : ∀ v, f v = c)
    (hc : ‖c‖ = 1) : edgeSum G oneKernel oneKernel_symm f = edgeCount G := by
  classical
  rw [edgeCount]
  have hcc : inner ℝ c c = 1 := by
    rw [real_inner_self_eq_norm_sq, hc]; norm_num
  unfold edgeSum
  trans ∑ e ∈ G.edgeFinset, (1 : ℝ)
  · exact Finset.sum_congr rfl fun e _ => by
      induction e using Sym2.inductionOn with
      | _ u v => rw [Sym2.lift_mk]; simp only [oneKernel, hf u, hf v, hcc, mul_one]
  · simp

/-- A unit vector of `ℓ²(ℝ)`. -/
def l2Unit : L2 := lp.single 2 (0 : ℕ) (1 : ℝ)

theorem norm_l2Unit : ‖l2Unit‖ = 1 := by
  rw [l2Unit, lp.norm_single (p := 2) (by norm_num)]
  norm_num

/-- A unit vector of `R^r` for `r ≥ 1`. -/
def finUnit (r : ℕ) (hr : 1 ≤ r) : EuclideanSpace ℝ (Fin r) :=
  PiLp.single 2 ⟨0, lt_of_lt_of_le Nat.zero_lt_one hr⟩ (1 : ℝ)

theorem norm_finUnit (r : ℕ) (hr : 1 ≤ r) : ‖finUnit r hr‖ = 1 := by
  rw [finUnit, PiLp.norm_single 2 (fun _ : Fin r => ℝ)]
  norm_num

/-- On a graph with an edge, the constant-`1` kernel gives a strictly positive `sdpInf`. -/
theorem sdpInf_oneKernel_pos (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) :
    0 < sdpInf G oneKernel oneKernel_symm := by
  classical
  have hcard : 0 < edgeCount G := by
    obtain ⟨u, v, huv⟩ := hne
    have hmem : s(u, v) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact huv
    have hpos : 0 < G.edgeFinset.card := Finset.card_pos.2 ⟨s(u, v), hmem⟩
    rw [edgeCount]
    exact_mod_cast hpos
  have h := edgeSum_le_sdpInf G oneKernel oneKernel_symm
    (fun _ => (l2Unit : L2)) (fun _ => norm_l2Unit)
  rw [edgeSum_oneKernel G (fun _ => (l2Unit : L2)) l2Unit (fun _ => rfl) norm_l2Unit] at h
  linarith

/-- On a graph with an edge, the constant-`1` kernel gives a strictly positive `sdpRank`. -/
theorem sdpRank_oneKernel_pos (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V)
    (hne : ∃ u v, G.Adj u v) : 0 < sdpRank r G oneKernel oneKernel_symm := by
  classical
  have hcard : 0 < edgeCount G := by
    obtain ⟨u, v, huv⟩ := hne
    have hmem : s(u, v) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact huv
    have hpos : 0 < G.edgeFinset.card := Finset.card_pos.2 ⟨s(u, v), hmem⟩
    rw [edgeCount]
    exact_mod_cast hpos
  have h := edgeSum_le_sdpRank r G oneKernel oneKernel_symm
    (fun _ => finUnit r hr) (fun _ => norm_finUnit r hr)
  rw [edgeSum_oneKernel G (fun _ => finUnit r hr) (finUnit r hr) (fun _ => rfl)
    (norm_finUnit r hr)] at h
  linarith

end ConstKernel

section Endgame

/-- If the graph has no edge, the edge set is empty. -/
theorem edgeSet_eq_empty_of_noEdge (G : SimpleGraph V) (hne : ¬ ∃ u v, G.Adj u v) :
    G.edgeSet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v => exact hne ⟨u, v, (SimpleGraph.mem_edgeSet G).1 he⟩



/-- If the graph has no edge, every edge sum vanishes, hence `sdpInf = 0`. -/
theorem sdpInf_eq_zero_of_noEdge (G : SimpleGraph V) (hne : ¬ ∃ u v, G.Adj u v) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) : sdpInf G A hA = 0 := by
  classical
  have hempty : G.edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have h1 : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).1 he
    rw [edgeSet_eq_empty_of_noEdge G hne] at h1
    exact h1
  have hzero : ∀ f : V → L2, edgeSum G A hA f = 0 := by
    intro f
    unfold edgeSum
    rw [hempty]
    simp
  have hsub : {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f} ⊆ {0} := by
    rintro x ⟨f, _, rfl⟩
    rw [hzero f]
    simp
  have hS : sdpInf G A hA = sSup {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧
      x = edgeSum G A hA f} := rfl
  rw [hS]
  rcases Set.eq_empty_or_nonempty {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧
      x = edgeSum G A hA f} with h | ⟨x, hx⟩
  · rw [h, Real.sSup_empty]
  · have hx0 : x = 0 := hsub hx
    have hset : {x : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f} = {0} := by
      ext y
      constructor
      · intro hy
        exact hsub hy
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy, ← hx0]
        exact hx
    rw [hset, csSup_singleton]

/-- If the graph has no edge, every edge sum vanishes, hence `sdpRank = 0`. -/
theorem sdpRank_eq_zero_of_noEdge (G : SimpleGraph V) (hne : ¬ ∃ u v, G.Adj u v) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) (r : ℕ) : sdpRank r G A hA = 0 := by
  classical
  have hempty : G.edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have h1 : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).1 he
    rw [edgeSet_eq_empty_of_noEdge G hne] at h1
    exact h1
  have hzero : ∀ f : V → EuclideanSpace ℝ (Fin r), edgeSum G A hA f = 0 := by
    intro f
    unfold edgeSum
    rw [hempty]
    simp
  have hsub : {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r), (∀ v, ‖f v‖ = 1) ∧
      x = edgeSum G A hA f} ⊆ {0} := by
    rintro x ⟨f, _, rfl⟩
    rw [hzero f]
    simp
  have hS : sdpRank r G A hA = sSup {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r),
      (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f} := rfl
  rw [hS]
  rcases Set.eq_empty_or_nonempty {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r),
      (∀ v, ‖f v‖ = 1) ∧ x = edgeSum G A hA f} with h | ⟨x, hx⟩
  · rw [h, Real.sSup_empty]
  · have hx0 : x = 0 := hsub hx
    have hset : {x : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r), (∀ v, ‖f v‖ = 1) ∧
        x = edgeSum G A hA f} = {0} := by
      ext y
      constructor
      · intro hy
        exact hsub hy
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy, ← hx0]
        exact hx
    rw [hset, csSup_singleton]

end Endgame

section GrothendieckConstantBound

/-- The set of constants dominated by `K(r,G)` is bounded below as soon as the graph has an
edge. -/
theorem bddBelow_grothendieckSet (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r)
    (hne : ∃ u v, G.Adj u v) :
    BddBelow {K : ℝ | ∀ (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u),
      sdpInf G A hA ≤ K * sdpRank r G A hA} := by
  refine ⟨0, ?_⟩
  intro K hK
  by_contra hneg
  push_neg at hneg
  have h1 : sdpInf G oneKernel oneKernel_symm ≤ K * sdpRank r G oneKernel oneKernel_symm :=
    hK _ _
  have h2 : 0 < sdpInf G oneKernel oneKernel_symm := sdpInf_oneKernel_pos G hne
  have h3 : 0 < sdpRank r G oneKernel oneKernel_symm := sdpRank_oneKernel_pos r hr G hne
  nlinarith

/-- **The endgame bookkeeping.** If every symmetric `A` satisfies `SDP_∞ ≤ κ · SDP_r`, then
`K(r,G) ≤ κ` (for `κ ≥ 0`, `1 ≤ r`).  This is the step from the algorithmic inequality to the
constant, used both for Theorem 1.2 and for Theorem 5.1. -/
theorem grothendieckConstant_le (G : SimpleGraph V) (r : ℕ) {κ : ℝ} (hr : 1 ≤ r) (hκ : 0 ≤ κ)
    (h : ∀ (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u),
      sdpInf G A hA ≤ κ * sdpRank r G A hA) :
    grothendieckConstant r G ≤ κ := by
  classical
  have hS : grothendieckConstant r G =
      sInf {K : ℝ | ∀ (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u),
        sdpInf G A hA ≤ K * sdpRank r G A hA} := rfl
  rw [hS]
  by_cases hne : ∃ u v, G.Adj u v
  · exact csInf_le (bddBelow_grothendieckSet G r hr hne) h
  · have hall : {K : ℝ | ∀ (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u),
        sdpInf G A hA ≤ K * sdpRank r G A hA} = Set.univ := by
      ext K
      constructor
      · intro _; trivial
      · intro _
        intro A hA
        rw [sdpInf_eq_zero_of_noEdge G hne A hA, sdpRank_eq_zero_of_noEdge G hne A hA r]
        simp
    rw [hall, Real.sInf_univ]
    exact hκ

end GrothendieckConstantBound


section Nonneg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sign of a subset, as a real number `±1`. -/
def sgnSet (X : Finset V) (u : V) : ℝ := if u ∈ X then 1 else -1

theorem abs_sgnSet (X : Finset V) (u : V) : |sgnSet X u| = 1 := by
  unfold sgnSet
  split <;> norm_num

/-- The family obtained by flipping a constant unit vector according to a sign pattern. -/
def flipFam (c : E) (X : Finset V) : V → E := fun u => sgnSet X u • c

theorem norm_flipFam {c : E} (hc : ‖c‖ = 1) (X : Finset V) (u : V) :
    ‖flipFam c X u‖ = 1 := by
  rw [flipFam, norm_smul, hc, mul_one, Real.norm_eq_abs, abs_sgnSet]

theorem inner_flipFam {c : E} (hc : ‖c‖ = 1) (X : Finset V) (u v : V) :
    inner ℝ (flipFam c X u) (flipFam c X v) = sgnSet X u * sgnSet X v := by
  have hcc : inner ℝ c c = 1 := by rw [real_inner_self_eq_norm_sq, hc]; norm_num
  simp only [flipFam]
  rw [real_inner_smul_left, real_inner_smul_right, hcc, mul_one]

/-- Summing a product of two coordinate signs over the power set of `V` gives zero. -/
theorem sum_powerset_sgnSet_mul {u v : V} (huv : u ≠ v) :
    ∑ X ∈ (Finset.univ : Finset V).powerset, sgnSet X u * sgnSet X v = 0 := by
  classical
  have hnot : u ∉ (Finset.univ : Finset V).erase u := Finset.notMem_erase u _
  have hins : insert u ((Finset.univ : Finset V).erase u) = (Finset.univ : Finset V) :=
    Finset.insert_erase (Finset.mem_univ u)
  rw [← hins, Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun X hX => ?_
  have huX : u ∉ X := fun h => hnot (Finset.mem_powerset.1 hX h)
  have hv : v ∈ insert u X ↔ v ∈ X := by
    rw [Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact absurd h.symm huv
      · exact h
    · intro h; exact Or.inr h
  have h1 : sgnSet X u = -1 := by simp [sgnSet, huX]
  have h2 : sgnSet (insert u X) u = 1 := by simp [sgnSet]
  have h3 : sgnSet (insert u X) v = sgnSet X v := by simp only [sgnSet, hv]
  rw [h1, h2, h3]
  ring

/-- `sdpRank r G A` is nonnegative: averaging the sign-flipped constant families gives `0`. -/
theorem sdpRank_nonneg (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) : 0 ≤ sdpRank r G A hA := by
  classical
  have hc : ‖finUnit r hr‖ = 1 := norm_finUnit r hr
  have hzero : ∑ X ∈ (Finset.univ : Finset V).powerset,
      edgeSum G A hA (flipFam (finUnit r hr) X) = 0 := by
    simp only [edgeSum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e he => ?_
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Sym2.lift_mk]
      have hne : u ≠ v := by
        rintro rfl
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact SimpleGraph.irrefl G he
      simp only [inner_flipFam hc]
      rw [← Finset.mul_sum, sum_powerset_sgnSet_mul hne, mul_zero]
  have hex : ∃ X ∈ (Finset.univ : Finset V).powerset,
      0 ≤ edgeSum G A hA (flipFam (finUnit r hr) X) := by
    by_contra h
    push Not at h
    have hlt := Finset.sum_neg (f := fun X => edgeSum G A hA (flipFam (finUnit r hr) X)) h
      ⟨∅, Finset.empty_mem_powerset (Finset.univ : Finset V)⟩
    rw [hzero] at hlt
    exact lt_irrefl 0 hlt
  obtain ⟨X, _, hX⟩ := hex
  exact le_trans hX (edgeSum_le_sdpRank r G A hA _ fun u => norm_flipFam hc X u)

/-- `sdpInf G A` is nonnegative, by the same sign-flip averaging. -/
theorem sdpInf_nonneg (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) :
    0 ≤ sdpInf G A hA := by
  classical
  have hc : ‖l2Unit‖ = 1 := norm_l2Unit
  have hzero : ∑ X ∈ (Finset.univ : Finset V).powerset,
      edgeSum G A hA (flipFam (l2Unit : L2) X) = 0 := by
    simp only [edgeSum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e he => ?_
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Sym2.lift_mk]
      have hne : u ≠ v := by
        rintro rfl
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        exact SimpleGraph.irrefl G he
      simp only [inner_flipFam hc]
      rw [← Finset.mul_sum, sum_powerset_sgnSet_mul hne, mul_zero]
  have hex : ∃ X ∈ (Finset.univ : Finset V).powerset,
      0 ≤ edgeSum G A hA (flipFam (l2Unit : L2) X) := by
    by_contra h
    push Not at h
    have hlt := Finset.sum_neg (f := fun X => edgeSum G A hA (flipFam (l2Unit : L2) X)) h
      ⟨∅, Finset.empty_mem_powerset (Finset.univ : Finset V)⟩
    rw [hzero] at hlt
    exact lt_irrefl 0 hlt
  obtain ⟨X, _, hX⟩ := hex
  exact le_trans hX (edgeSum_le_sdpInf G A hA _ fun u => norm_flipFam hc X u)

end Nonneg

section DoubleCounting

/-- Single-edge case of the double counting. -/
theorem sum_prod_single {F : V → V → ℝ} (hF : ∀ u v, F u v = F v u) {x y : V} (hxy : x ≠ y) :
    ∑ u, ∑ v, (if s(u, v) = s(x, y) then F u v else 0) = 2 * F x y := by
  classical
  rw [← Fintype.sum_prod_type (fun p : V × V => if s(p.1, p.2) = s(x, y) then F p.1 p.2 else 0)]
  rw [← Finset.sum_filter]
  have hfilt : (Finset.univ.filter fun p : V × V => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases (Sym2.mk_eq_mk_iff (p := p) (q := (x, y))).1 h with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
    · rintro (rfl | rfl)
      · rfl
      · simp
  rw [hfilt]
  have hne : (x, y) ≠ (y, x) := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact hxy h.1
  rw [Finset.sum_pair hne, hF y x]
  ring

/-- A single edge (no loop) case, in `Sym2` form. -/
theorem two_mul_lift_of_noLoop {F : V → V → ℝ} (hF : ∀ u v, F u v = F v u) {a : Sym2 V}
    (ha : ∀ x : V, a ≠ s(x, x)) :
    ∑ u, ∑ v, (if s(u, v) = a then F u v else 0) = 2 * Sym2.lift ⟨F, hF⟩ a := by
  induction a using Sym2.inductionOn with
  | _ x y =>
    rw [Sym2.lift_mk]
    have hxy : x ≠ y := by
      rintro rfl
      exact ha x rfl
    exact sum_prod_single hF hxy

/-- **Double counting.** For a set `L` of unordered non-loop pairs, the sum of a symmetric
kernel over ordered pairs is twice the sum over `L`. -/
theorem two_mul_sum_lift {F : V → V → ℝ} (hF : ∀ u v, F u v = F v u) :
    ∀ (L : Finset (Sym2 V)), (∀ a ∈ L, ∀ x : V, a ≠ s(x, x)) →
      2 * (∑ e ∈ L, Sym2.lift ⟨F, hF⟩ e)
        = ∑ u, ∑ v, (if s(u, v) ∈ L then F u v else 0) := by
  intro L
  induction L using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert a L' ha ih =>
    intro hside
    have hside' : ∀ b ∈ L', ∀ x : V, b ≠ s(x, x) := fun b hb => hside b (Finset.mem_insert_of_mem hb)
    have ha' : ∀ x : V, a ≠ s(x, x) := fun x => hside a (Finset.mem_insert_self a L') x
    have hsplit : ∀ u v : V, (if s(u, v) ∈ insert a L' then F u v else 0)
        = (if s(u, v) = a then F u v else 0) + (if s(u, v) ∈ L' then F u v else 0) := by
      intro u v
      by_cases h1 : s(u, v) = a
      · have hmem : s(u, v) ∈ insert a L' := by rw [h1]; exact Finset.mem_insert_self a L'
        have hnot : s(u, v) ∉ L' := by rw [h1]; exact ha
        rw [if_pos hmem, if_neg hnot, if_pos h1]
        ring
      · by_cases h2 : s(u, v) ∈ L'
        · have hmem : s(u, v) ∈ insert a L' := Finset.mem_insert_of_mem h2
          rw [if_pos hmem, if_neg h1, if_pos h2]
          ring
        · have hmem : s(u, v) ∉ insert a L' := by
            intro hcon
            rcases Finset.mem_insert.1 hcon with h | h
            · exact h1 h
            · exact h2 h
          rw [if_neg hmem, if_neg h1, if_neg h2]
          ring
    have key : ∑ u, ∑ v, (if s(u, v) ∈ insert a L' then F u v else 0)
        = 2 * Sym2.lift ⟨F, hF⟩ a + ∑ u, ∑ v, (if s(u, v) ∈ L' then F u v else 0) := by
      rw [show (∑ u, ∑ v, (if s(u, v) ∈ insert a L' then F u v else 0))
          = ∑ u, ∑ v, ((if s(u, v) = a then F u v else 0) +
              (if s(u, v) ∈ L' then F u v else 0)) from
            Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hsplit u v]
      simp only [Finset.sum_add_distrib]
      rw [two_mul_lift_of_noLoop hF ha']
    rw [Finset.sum_insert ha, mul_add, ih hside', key]


end DoubleCounting

/-- The ordered-pair form of the edge sum (with the classical decidability built in). -/
def edgePairSum (G : SimpleGraph V) (A : V → V → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : V → E) : ℝ := by
  classical
  exact ∑ u, ∑ v, (if G.Adj u v then A u v * inner ℝ (f u) (f v) else 0)

/-- **Double counting for the edge sum.**  `2 · edgeSum` is the sum over ordered adjacent
pairs. -/
theorem two_mul_edgeSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) (f : V → E) :
    2 * edgeSum G A hA f = edgePairSum G A f := by
  classical
  have hF : ∀ u v : V, (fun u v => A u v * inner ℝ (f u) (f v)) u v =
      (fun u v => A u v * inner ℝ (f u) (f v)) v u := by
    intro u v
    simp only [hA u v, real_inner_comm]
  have hno : ∀ a ∈ G.edgeFinset, ∀ x : V, a ≠ s(x, x) := by
    intro a ha x hcon
    have h1 : a ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).1 ha
    rw [hcon] at h1
    rw [SimpleGraph.mem_edgeSet] at h1
    exact SimpleGraph.irrefl G h1
  have key := two_mul_sum_lift hF G.edgeFinset hno
  have hval : edgeSum G A hA f =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => A u v * inner ℝ (f u) (f v), hF⟩ e := by
    unfold edgeSum
    exact Finset.sum_congr rfl fun e _ =>
      congrArg (fun g : {g : V → V → ℝ // ∀ a₁ a₂, g a₁ a₂ = g a₂ a₁} => Sym2.lift g e)
        (Subtype.ext rfl)
  rw [hval, key, edgePairSum]
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]


section BallSphere

variable {r : ℕ}

/-- The vector `v` placed at the single coordinate `u`. -/
def deltaAt (u : V) (v : EuclideanSpace ℝ (Fin r)) : V → EuclideanSpace ℝ (Fin r) :=
  fun z => if z = u then v else 0

theorem deltaAt_self (u : V) (v : EuclideanSpace ℝ (Fin r)) : deltaAt u v u = v := by
  simp [deltaAt]

theorem deltaAt_other {u z : V} (hz : z ≠ u) (v : EuclideanSpace ℝ (Fin r)) :
    deltaAt u v z = 0 := by
  simp [deltaAt, hz]

/-- The "best response" vector at `u`: the gradient of the edge sum in the `u`-th coordinate. -/
def respVec (G : SimpleGraph V) (A : V → V → ℝ) (f : V → EuclideanSpace ℝ (Fin r)) (u : V) :
    EuclideanSpace ℝ (Fin r) := by
  classical
  exact ∑ w, (if G.Adj u w then A u w • f w else 0)

/-- The ordered-pair bilinear form of a symmetric kernel. -/
def pairSumOp (G : SimpleGraph V) (A : V → V → ℝ)
    (f g : V → EuclideanSpace ℝ (Fin r)) : ℝ := by
  classical
  exact ∑ x, ∑ w, (if G.Adj x w then A x w * inner ℝ (f x) (g w) else 0)

theorem two_mul_edgeSum' (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → EuclideanSpace ℝ (Fin r)) : 2 * edgeSum G A hA f = pairSumOp G A f f :=
  two_mul_edgeSum G A hA f

/-- A sum of a function supported at one point. -/
theorem sum_single_support {β : Type*} [AddCommMonoid β] {g : V → β} {u : V}
    (h : ∀ x, x ≠ u → g x = 0) : ∑ x, g x = g u :=
  Finset.sum_eq_single u (fun x _ hx => h x hx) (fun hc => absurd (Finset.mem_univ u) hc)

/-- `∑_w A(u,w)·⟨v, f w⟩ = ⟨v, respVec⟩` over the neighbours of `u`. -/
theorem sum_inner_respVec (G : SimpleGraph V) [DecidableRel G.Adj] (A : V → V → ℝ)
    (f : V → EuclideanSpace ℝ (Fin r)) (u : V) (v : EuclideanSpace ℝ (Fin r)) :
    ∑ w, (if G.Adj u w then A u w * inner ℝ v (f w) else 0) = inner ℝ v (respVec G A f u) := by
  classical
  rw [respVec, inner_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : G.Adj u w
  · rw [if_pos hw, if_pos hw, real_inner_smul_right]
  · rw [if_neg hw, if_neg hw]; simp

/-- The `delta`-in-the-first-slot term of the update formula. -/
theorem pairSum_delta_f (G : SimpleGraph V) (A : V → V → ℝ)
    (f : V → EuclideanSpace ℝ (Fin r)) (u : V) (v : EuclideanSpace ℝ (Fin r)) :
    pairSumOp G A (deltaAt u v) f = inner ℝ v (respVec G A f u) := by
  classical
  rw [pairSumOp]
  have hzero : ∀ x, x ≠ u → (∑ w, (if G.Adj x w then A x w * inner ℝ (deltaAt u v x)
      (f w) else 0)) = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [deltaAt_other hx]
    simp
  rw [sum_single_support hzero, deltaAt_self]
  exact sum_inner_respVec G A f u v

/-- The `delta`-in-the-second-slot term of the update formula. -/
theorem pairSum_delta_right (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → EuclideanSpace ℝ (Fin r)) (u : V) (v : EuclideanSpace ℝ (Fin r)) :
    pairSumOp G A f (deltaAt u v) = inner ℝ v (respVec G A f u) := by
  classical
  rw [pairSumOp]
  have hinner : ∀ x, (∑ w, (if G.Adj x w then A x w * inner ℝ (f x) (deltaAt u v w) else 0))
      = (if G.Adj x u then A x u * inner ℝ (f x) v else 0) := by
    intro x
    trans (if G.Adj x u then A x u * inner ℝ (f x) (deltaAt u v u) else 0)
    · exact Finset.sum_eq_single u
        (fun w _ hw => by rw [deltaAt_other hw]; simp)
        (fun hc => absurd (Finset.mem_univ u) hc)
    · rw [deltaAt_self]
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  rw [show (∑ x, (if G.Adj x u then A x u * inner ℝ (f x) v else 0))
      = ∑ x, (if G.Adj u x then A u x * inner ℝ v (f x) else 0) from
    Finset.sum_congr rfl fun x _ => by
      by_cases hx : G.Adj x u
      · rw [if_pos hx, if_pos ((G.adj_comm u x).2 hx), hA x u, real_inner_comm]
      · rw [if_neg hx, if_neg (fun h => hx ((G.adj_comm u x).1 h))]]
  exact sum_inner_respVec G A f u v

/-- The `delta`-`delta` term vanishes (no loops). -/
theorem pairSum_delta_delta (G : SimpleGraph V) (A : V → V → ℝ)
    (u : V) (v : EuclideanSpace ℝ (Fin r)) :
    pairSumOp G A (deltaAt u v) (deltaAt u v) = 0 := by
  classical
  rw [pairSumOp]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x = u
  · rw [hx]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hw : w = u
    · rw [hw, if_neg (G.irrefl)]
    · rw [deltaAt_other hw]
      simp
  · rw [deltaAt_other hx]
    simp

theorem pairSum_add_left (G : SimpleGraph V) (A : V → V → ℝ)
    (f₁ f₂ g : V → EuclideanSpace ℝ (Fin r)) :
    pairSumOp G A (fun z => f₁ z + f₂ z) g = pairSumOp G A f₁ g + pairSumOp G A f₂ g := by
  classical
  rw [pairSumOp, pairSumOp, pairSumOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : G.Adj x w
  · rw [if_pos hw, if_pos hw, if_pos hw, inner_add_left, mul_add]
  · rw [if_neg hw, if_neg hw, if_neg hw]; ring

theorem pairSum_add_right (G : SimpleGraph V) (A : V → V → ℝ)
    (f g₁ g₂ : V → EuclideanSpace ℝ (Fin r)) :
    pairSumOp G A f (fun z => g₁ z + g₂ z) = pairSumOp G A f g₁ + pairSumOp G A f g₂ := by
  classical
  rw [pairSumOp, pairSumOp, pairSumOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : G.Adj x w
  · rw [if_pos hw, if_pos hw, if_pos hw, inner_add_right, mul_add]
  · rw [if_neg hw, if_neg hw, if_neg hw]; ring

/-- **Update formula.** Changing one coordinate of a family changes the edge sum by the inner
product of the change with the best-response vector at that coordinate. -/
theorem edgeSum_update (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    (f : V → EuclideanSpace ℝ (Fin r)) (u : V) (y : EuclideanSpace ℝ (Fin r)) :
    edgeSum G A hA (Function.update f u y)
      = edgeSum G A hA f + inner ℝ (y - f u) (respVec G A f u) := by
  classical
  set v : EuclideanSpace ℝ (Fin r) := y - f u with hv
  have hf' : Function.update f u y = fun z => f z + deltaAt u v z := by
    funext z
    by_cases hz : z = u
    · subst hz
      rw [Function.update_apply, if_pos rfl]
      simp [deltaAt, hv]
    · rw [Function.update_of_ne hz, deltaAt_other hz]
      simp
  have key : 2 * edgeSum G A hA (Function.update f u y)
      = 2 * edgeSum G A hA f + 2 * inner ℝ v (respVec G A f u) := by
    rw [hf', two_mul_edgeSum', pairSum_add_left, pairSum_add_right, pairSum_add_right,
      pairSum_delta_f G A f u v, pairSum_delta_right G A hA f u v,
      pairSum_delta_delta G A u v, two_mul_edgeSum']
    ring
  rw [hv] at key ⊢
  linarith


/-- Pushing one coordinate to the unit sphere never decreases the edge sum. -/
theorem exists_push_ge (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    {r : ℕ} (hr : 1 ≤ r) (f : V → EuclideanSpace ℝ (Fin r)) (u : V) (hu : ‖f u‖ ≤ 1) :
    ∃ y : EuclideanSpace ℝ (Fin r), ‖y‖ = 1 ∧
      edgeSum G A hA f ≤ edgeSum G A hA (Function.update f u y) := by
  classical
  by_cases hv : respVec G A f u = 0
  · refine ⟨finUnit r hr, norm_finUnit r hr, ?_⟩
    rw [edgeSum_update, hv, inner_zero_right, add_zero]
  · set c := respVec G A f u with hc
    have hc0 : c ≠ 0 := hv
    have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc0
    refine ⟨(‖c‖)⁻¹ • c, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hcn)]
    · have hinner : inner ℝ ((‖c‖)⁻¹ • c - f u) c = ‖c‖ - inner ℝ (f u) c := by
        rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      have hle : inner ℝ (f u) c ≤ ‖c‖ := by
        calc inner ℝ (f u) c ≤ |inner ℝ (f u) c| := le_abs_self _
          _ ≤ ‖f u‖ * ‖c‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * ‖c‖ := by
              exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)
          _ = ‖c‖ := one_mul _
      rw [edgeSum_update, hinner]
      linarith

/-- **Ball-to-sphere.**  A family of vectors of norm at most one is dominated by `sdpRank`. -/
theorem edgeSum_le_sdpRank_aux (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u)
    {r : ℕ} (hr : 1 ≤ r) :
    ∀ s : Finset V, ∀ f : V → EuclideanSpace ℝ (Fin r),
      (∀ v ∈ s, ‖f v‖ ≤ 1) → (∀ v, v ∉ s → ‖f v‖ = 1) →
      edgeSum G A hA f ≤ sdpRank r G A hA := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f _ hf
    exact edgeSum_le_sdpRank r G A hA f (fun v => hf v (Finset.notMem_empty v))
  | insert u s' hu ih =>
    intro f hfs hfout
    obtain ⟨y, hy, hge⟩ := exists_push_ge G A hA hr f u (hfs u (Finset.mem_insert_self u s'))
    refine le_trans hge (ih (Function.update f u y) ?_ ?_)
    · intro v hv
      by_cases hvu : v = u
      · rw [hvu, Function.update_apply, if_pos rfl]
        exact le_of_eq hy
      · rw [Function.update_of_ne hvu]
        exact hfs v (Finset.mem_insert_of_mem hv)
    · intro v hv
      by_cases hvu : v = u
      · rw [hvu, Function.update_apply, if_pos rfl]
        exact hy
      · rw [Function.update_of_ne hvu]
        refine hfout v ?_
        intro hmem
        rcases Finset.mem_insert.1 hmem with h | h
        · exact hvu h
        · exact hv h

/-- **Ball-to-sphere, final form.**  For `1 ≤ r`, the edge sum of a family of vectors of norm at
most one is at most `sdpRank r G A`.  (The paper's §5 rounding produces exactly such families, so
this is what makes its step `SDP_r ≥ E[∑ A_e g_u·g_v]` rigorous.) -/
theorem edgeSum_le_sdpRank_of_norm_le (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) {r : ℕ} (hr : 1 ≤ r) (f : V → EuclideanSpace ℝ (Fin r))
    (hf : ∀ v, ‖f v‖ ≤ 1) : edgeSum G A hA f ≤ sdpRank r G A hA :=
  edgeSum_le_sdpRank_aux G A hA hr Finset.univ f (fun v _ => hf v)
    (fun v hv => absurd (Finset.mem_univ v) hv)

end BallSphere


section RankMono

/-- Pad a vector of `R^r` with zeros to `R^{r'}`. -/
def padVec {r r' : ℕ} (hr : r ≤ r') (x : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℝ (Fin r') :=
  WithLp.toLp 2 fun i : Fin r' => if h : (i : ℕ) < r then x.ofLp ⟨i.1, h⟩ else 0

theorem padVec_ofLp {r r' : ℕ} (hr : r ≤ r') (x : EuclideanSpace ℝ (Fin r)) (i : Fin r') :
    (padVec hr x).ofLp i = if h : (i : ℕ) < r then x.ofLp ⟨i.1, h⟩ else 0 := rfl

theorem sum_pad {r r' : ℕ} (hr : r ≤ r') (g : Fin r → ℝ) :
    ∑ i : Fin r', (if h : (i : ℕ) < r then g ⟨i.1, h⟩ else 0) = ∑ j : Fin r, g j := by
  classical
  set G : Fin r' → ℝ := fun i => if h : (i : ℕ) < r then g ⟨i.1, h⟩ else 0 with hG
  set ψ : Fin r → Fin r' := fun j => (⟨j.1, lt_of_lt_of_le j.2 hr⟩ : Fin r') with hψ
  have hsub : (Finset.univ.filter fun i : Fin r' => (i : ℕ) < r) ⊆
      (Finset.univ : Finset (Fin r')) := Finset.filter_subset _ _
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin r')), i ∉
      (Finset.univ.filter fun i : Fin r' => (i : ℕ) < r) → G i = 0 := by
    intro i _ hi
    rw [hG]
    by_cases h : (i : ℕ) < r
    · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩) hi
    · exact dif_neg h
  have himg : (Finset.univ.filter fun i : Fin r' => (i : ℕ) < r) =
      (Finset.univ : Finset (Fin r)).image ψ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨⟨i.1, h⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin r)), ∀ y ∈ Finset.univ, ψ x = ψ y → x = y := by
    intro x _ y _ hxy
    exact Fin.ext (by simpa [hψ] using congrArg Fin.val hxy)
  rw [← Finset.sum_subset hsub hzero, himg]
  trans ∑ j : Fin r, G (ψ j)
  · exact Finset.sum_image hinj
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hG]
    exact dif_pos j.2

theorem inner_padVec {r r' : ℕ} (hr : r ≤ r') (x y : EuclideanSpace ℝ (Fin r)) :
    inner ℝ (padVec hr x) (padVec hr y) = inner ℝ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hterm : ∀ i : Fin r', inner ℝ ((padVec hr x).ofLp i) ((padVec hr y).ofLp i)
      = (if h : (i : ℕ) < r then inner ℝ (x.ofLp ⟨i.1, h⟩) (y.ofLp ⟨i.1, h⟩) else 0) := by
    intro i
    by_cases h : (i : ℕ) < r <;> simp [padVec_ofLp, h]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact sum_pad hr (fun j => inner ℝ (x.ofLp j) (y.ofLp j))


/-- `sdpRank` is monotone in the rank. -/
theorem sdpRank_mono {r r' : ℕ} (hr : 1 ≤ r) (hrr' : r ≤ r') (G : SimpleGraph V)
    (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) :
    sdpRank r G A hA ≤ sdpRank r' G A hA := by
  classical
  refine csSup_le
    ⟨edgeSum G A hA (fun _ => finUnit r hr), (fun _ => finUnit r hr),
      (fun _ => norm_finUnit r hr), rfl⟩ ?_
  rintro x ⟨f, hf, rfl⟩
  have hval : edgeSum G A hA f = edgeSum G A hA (fun v => padVec hrr' (f v)) := by
    unfold edgeSum
    refine Finset.sum_congr rfl fun e _ => ?_
    induction e using Sym2.inductionOn with
    | _ u v => simp only [Sym2.lift_mk, inner_padVec]
  rw [hval]
  refine edgeSum_le_sdpRank r' G A hA (fun v => padVec hrr' (f v)) ?_
  intro v
  have h1 : inner ℝ (padVec hrr' (f v)) (padVec hrr' (f v)) = 1 := by
    rw [inner_padVec, real_inner_self_eq_norm_sq, hf v]
    norm_num
  have h2 : ‖padVec hrr' (f v)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact h1
  nlinarith [norm_nonneg (padVec hrr' (f v))]

end RankMono

section Approximation

/-- If `x < sdpInf` there is a unit family whose edge sum exceeds `x`. -/
theorem exists_edgeSum_gt_of_lt_sdpInf (G : SimpleGraph V) (A : V → V → ℝ)
    (hA : ∀ u v, A u v = A v u) {x : ℝ} (hx : x < sdpInf G A hA) :
    ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ x < edgeSum G A hA f := by
  obtain ⟨y, ⟨f, hf, rfl⟩, hxy⟩ := exists_lt_of_lt_csSup
    (s := {y : ℝ | ∃ f : V → L2, (∀ v, ‖f v‖ = 1) ∧ y = edgeSum G A hA f})
    ⟨edgeSum G A hA (fun _ => l2Unit), (fun _ => l2Unit), (fun _ => norm_l2Unit), rfl⟩ hx
  exact ⟨f, hf, hxy⟩

/-- If `x < sdpRank r` (`1 ≤ r`) there is a unit family whose edge sum exceeds `x`. -/
theorem exists_edgeSum_gt_of_lt_sdpRank (r : ℕ) (hr : 1 ≤ r) (G : SimpleGraph V)
    (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) {x : ℝ} (hx : x < sdpRank r G A hA) :
    ∃ f : V → EuclideanSpace ℝ (Fin r), (∀ v, ‖f v‖ = 1) ∧ x < edgeSum G A hA f := by
  obtain ⟨y, ⟨f, hf, rfl⟩, hxy⟩ := exists_lt_of_lt_csSup
    (s := {y : ℝ | ∃ f : V → EuclideanSpace ℝ (Fin r), (∀ v, ‖f v‖ = 1) ∧
      y = edgeSum G A hA f})
    ⟨edgeSum G A hA (fun _ => finUnit r hr), (fun _ => finUnit r hr),
      (fun _ => norm_finUnit r hr), rfl⟩ hx
  exact ⟨f, hf, hxy⟩

end Approximation

/-! ## Axiom checks -/


end Grothendieck

open Grothendieck in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {r r' : ℕ} (hr : 1 ≤ r) (hrr' : r ≤ r')
    (G : SimpleGraph V) (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) :
    sdpRank r G A hA ≤ sdpRank r' G A hA :=
  Grothendieck.sdpRank_mono hr hrr' G A hA
