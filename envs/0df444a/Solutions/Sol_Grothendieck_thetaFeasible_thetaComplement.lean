-- Prove2me | solution 1 for Grothendieck.thetaFeasible_thetaComplement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:08:06.467297+00:00
-- url     : https://prove2.me/submissions/90b48a57-8b48-4cbf-a131-cb683e449464

import Mathlib
import Definitions.Def_Grothendieck_Theta

set_option autoImplicit false

/-!
# Attainment of the theta-program optimum (the `hZ` hypothesis of Lemma 4.1)

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs
with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105, equation (4.1), p. 92.

`thetaComplement G` is defined as the infimum of the feasible values of the semidefinite
program

  `ϑ(G) = min { λ : Z ⪰ 0, Z(u,u) = λ - 1 for all u, Z(u,v) = -1 for {u,v} ∈ E }`.

The published reduction `Grothendieck.vector_construction_of_theta` (Lemma 4.1) takes as a
hypothesis

  `hZ : ∃ Z, Z.PosSemidef ∧ (∀ u, Z u u = thetaComplement G - 1) ∧ ∀ u v, G.Adj u v → Z u v = -1`,

i.e. exactly the statement that this infimum is *attained*.  This file proves it, so that `hZ`
is discharged and `vector_construction_of_theta` applies with one hypothesis fewer.

The argument completes the proof of Proposition 4.2 (p. 93), whose lower bound `ϑ(G) ≥ 2` is
already published as `theta_ge_two` (and reproved here, as the published proof may not be
imported):

* `thetaFeasible_card` — the program is feasible (`λ = |V|`, the regular simplex of p. 92);
* `le_of_thetaFeasible` — every feasible `λ` satisfies `λ ≥ 2`, so `2 ≤ ϑ(G) ≤ |V|`;
* hence a minimising sequence `λ_n → ϑ(G)` lies in `[2, |V| + 1]`;
* positive semidefiniteness gives `Z(u,v)² ≤ Z(u,u) Z(v,v) = (λ-1)²`, so the corresponding
  matrices all lie in the compact box `[-|V|, |V|]^{V × V}`, and a subsequence converges;
* the limit is again positive semidefinite — the cone is closed, being cut out by the
  continuous conditions `star x ⬝ᵥ Z *ᵥ x ≥ 0` — has the same diagonal and the same `-1`
  entries across edges, and its diagonal is `ϑ(G) - 1`.
-/

noncomputable section

open scoped BigOperators Real Topology
open Filter

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The published proof of `theta_ge_two`, with its pointwise core exposed -/

omit [Fintype V] [DecidableEq V] in
/-- Positive semidefinite matrices satisfy `Z u v ^ 2 ≤ Z u u * Z v v`: apply positive
semidefiniteness to the `2 × 2` principal submatrix on `{u, v}` and use that its determinant
is nonnegative. -/
theorem posSemidef_sq_le_diag {Z : Matrix V V ℝ} (hZ : Z.PosSemidef) (u v : V) :
    Z u v ^ 2 ≤ Z u u * Z v v := by
  have hsub := hZ.submatrix (fun i : Fin 2 => ![u, v] i)
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hsymm : Z v u = Z u v := by
    have h := hZ.isHermitian.apply u v
    simpa using h
  rw [hsymm] at hdet
  nlinarith

/-- The Laplacian matrix of the complete graph on `V` is a feasible solution of the theta
program (4.1) with `λ = |V|`: it is positive semidefinite, its diagonal is `|V| - 1` and its
off-diagonal entries are `-1`. -/
theorem thetaFeasible_card (G : SimpleGraph V) :
    ThetaFeasible G (Fintype.card V : ℝ) := by
  classical
  refine ⟨(⊤ : SimpleGraph V).lapMatrix ℝ, SimpleGraph.posSemidef_lapMatrix (R := ℝ) _, ?_, ?_⟩
  · intro u
    have hne : ({u} : Finset V)ᶜ.card = Fintype.card V - 1 := by
      rw [Finset.card_compl, Finset.card_singleton]
    have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
    simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      SimpleGraph.degree, SimpleGraph.neighborFinset, Matrix.sub_apply, Matrix.diagonal_apply,
      SimpleGraph.top_adj, reduceIte]
    simp [hne, Nat.cast_sub hpos]
  · intro u v huv
    have huv' : u ≠ v := huv.ne
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
      SimpleGraph.degree, SimpleGraph.neighborFinset, huv']

/-- Every feasible value of the theta program (4.1) is at least `2`, provided `G` has an edge:
positive semidefiniteness applied to the two endpoints of an edge gives
`1 = Z(u,v)² ≤ Z(u,u) Z(v,v) = (λ-1)²`, while `Z(u,u) ≥ 0` gives `λ ≥ 1`. -/
theorem le_of_thetaFeasible (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) {lam : ℝ}
    (hlam : ThetaFeasible G lam) : 2 ≤ lam := by
  obtain ⟨Z, hZ, hd, he⟩ := hlam
  obtain ⟨u, v, huv⟩ := hne
  have h1 : 0 ≤ lam - 1 := by
    have := hZ.diag_nonneg (i := u)
    rw [hd u] at this
    exact this
  have h3 : (1 : ℝ) ≤ (lam - 1) ^ 2 := by
    have hkey := posSemidef_sq_le_diag hZ u v
    rw [he u v huv, hd u, hd v] at hkey
    nlinarith
  nlinarith

/-- Every feasible value of the theta program (4.1) is at least `1`: `Z(u,u) = λ - 1 ≥ 0`. -/
theorem one_le_of_thetaFeasible [Nonempty V] (G : SimpleGraph V) {lam : ℝ}
    (hlam : ThetaFeasible G lam) : 1 ≤ lam := by
  obtain ⟨Z, hZ, hd, _he⟩ := hlam
  obtain ⟨u⟩ := ‹Nonempty V›
  have := hZ.diag_nonneg (i := u)
  rw [hd u] at this
  linarith

/-- For a graph `G` with at least one edge, the theta number of its complement is at least
`2` (p. 93). -/
theorem theta_ge_two_proof (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) :
    2 ≤ thetaComplement G := by
  refine le_csInf ⟨_, thetaFeasible_card G⟩ ?_
  intro lam hlam
  exact le_of_thetaFeasible G hne hlam

/-! ## 2. The quadratic form as an explicit double sum -/

/-- `star x ⬝ᵥ Z *ᵥ x` written as a sum over the entries of `Z`, so that convergence of the
entries gives convergence of the quadratic form. -/
theorem dotProduct_mulVec_eq_sum (x : V → ℝ) (M : Matrix V V ℝ) :
    star x ⬝ᵥ (M.mulVec x) = ∑ p : V × V, star (x p.1) * M p.1 p.2 * x p.2 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  simp only [Prod.fst, Prod.snd, star_trivial]
  ring

/-! ## 3. Attainment -/

/-- **The theta program (4.1) attains its optimum.**  For a graph with at least one edge there
is a positive semidefinite matrix `Z` with `Z u u = ϑ(G) - 1` and `Z u v = -1` across every
edge.  This is precisely hypothesis `hZ` of `Grothendieck.vector_construction_of_theta`. -/
theorem thetaFeasible_thetaComplement_proof (G : SimpleGraph V) [Nonempty V] :
    ThetaFeasible G (thetaComplement G) := by
  classical
  change ThetaFeasible G (sInf {lam : ℝ | ThetaFeasible G lam})
  set c : ℝ := sInf {lam : ℝ | ThetaFeasible G lam} with hc
  -- the two published bounds: the program is feasible, and every value is at least two
  have hneS : {lam : ℝ | ThetaFeasible G lam}.Nonempty := ⟨_, thetaFeasible_card G⟩
  have hbdd : BddBelow {lam : ℝ | ThetaFeasible G lam} :=
    ⟨1, fun _ hl => one_le_of_thetaFeasible G hl⟩
  have hc_le : c ≤ (Fintype.card V : ℝ) := csInf_le hbdd (thetaFeasible_card G)
  -- a minimising sequence
  have hchoice : ∀ n : ℕ, ∃ l : ℝ, ThetaFeasible G l ∧ l < c + 1 / (n + 1) := by
    intro n
    refine exists_lt_of_csInf_lt hneS ?_
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_add_of_pos_right c hpos
  choose u huS huc using hchoice
  have hu_tendsto : Tendsto u atTop (𝓝 c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (f := u) (g := fun _ => c)
      (h := fun n => c + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ ?_ ?_
    · simpa using (tendsto_const_nhds (x := c)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · intro n
      exact csInf_le hbdd (huS n)
    · intro n
      exact le_of_lt (huc n)
  -- the corresponding feasible matrices
  have huS' : ∀ n, ∃ Z : Matrix V V ℝ, Z.PosSemidef ∧ (∀ i, Z i i = u n - 1) ∧
      ∀ i j, G.Adj i j → Z i j = -1 := fun n => huS n
  choose Z hZPSD hZdiag hZedge using huS'
  -- uniform bound on the entries
  have hB : ∀ (n : ℕ) (i j : V), |Z n i j| ≤ (Fintype.card V : ℝ) := by
    intro n i j
    have hupper : u n - 1 ≤ (Fintype.card V : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [one_div]
        exact inv_le_one_of_one_le₀ hn1
      have h1 : u n < c + 1 / ((n : ℝ) + 1) := huc n
      linarith
    have hsq := posSemidef_sq_le_diag (hZPSD n) i j
    rw [hZdiag n i, hZdiag n j] at hsq
    have hsq2 : Z n i j ^ 2 ≤ (u n - 1) ^ 2 := by
      rw [pow_two (u n - 1)]
      exact hsq
    have h2 := one_le_of_thetaFeasible G (huS n)
    have h1 := abs_le_of_sq_le_sq hsq2 (by linarith : (0 : ℝ) ≤ u n - 1)
    exact le_trans h1 hupper
  -- compactness: extract a convergent subsequence of the matrices
  obtain ⟨w, _hwmem, φ, hφmono, hφtend⟩ :=
    (isCompact_univ_pi (fun _ : V × V => (isCompact_Icc : IsCompact
      (Set.Icc (-(Fintype.card V : ℝ)) (Fintype.card V : ℝ))))).tendsto_subseq
      (x := fun n p => Z n p.1 p.2) (fun n => by
        rw [Set.mem_pi]
        intro p _
        exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le (Z n p.1 p.2), hB n p.1 p.2],
          by linarith [le_abs_self (Z n p.1 p.2), hB n p.1 p.2]⟩)
  -- the limit matrix
  set Zlim : Matrix V V ℝ := fun i j => w (i, j) with hZlim
  have hcoord : ∀ i j : V, Tendsto (fun n => Z (φ n) i j) atTop (𝓝 (Zlim i j)) := by
    intro i j
    have h := (tendsto_pi_nhds.mp hφtend) (i, j)
    simpa [Function.comp_def, hZlim] using h
  -- it is Hermitian
  have hsymm : Zlim.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    rw [Matrix.conjTranspose_apply]
    have h1 : Tendsto (fun n => Z (φ n) i j) atTop (𝓝 (Zlim i j)) := hcoord i j
    have h2 : Tendsto (fun n => Z (φ n) i j) atTop (𝓝 (Zlim j i)) := by
      have hseq : (fun n => Z (φ n) j i) = fun n => Z (φ n) i j := by
        funext n
        have hh := (hZPSD (φ n)).isHermitian.apply i j
        simpa using hh
      rw [← hseq]
      exact hcoord j i
    have h3 := tendsto_nhds_unique h1 h2
    rw [← h3]
    simp
  -- it is positive semidefinite
  have hquad : ∀ x : V → ℝ, 0 ≤ star x ⬝ᵥ (Zlim.mulVec x) := by
    intro x
    rw [dotProduct_mulVec_eq_sum]
    have hsum : Tendsto (fun n => ∑ p : V × V,
        star (x p.1) * Z (φ n) p.1 p.2 * x p.2) atTop
        (𝓝 (∑ p : V × V, star (x p.1) * Zlim p.1 p.2 * x p.2)) := by
      refine tendsto_finsetSum Finset.univ ?_
      intro p _
      have h1 : Tendsto (fun n => star (x p.1) * Z (φ n) p.1 p.2) atTop
          (𝓝 (star (x p.1) * Zlim p.1 p.2)) :=
        tendsto_const_nhds.mul (hcoord p.1 p.2)
      exact h1.mul tendsto_const_nhds
    refine ge_of_tendsto (x := atTop) hsum (Eventually.of_forall fun n => ?_)
    rw [← dotProduct_mulVec_eq_sum]
    exact (hZPSD (φ n)).dotProduct_mulVec_nonneg x
  have hPSD : Zlim.PosSemidef :=
    Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hsymm, hquad⟩
  -- its diagonal is `c - 1`
  have hdiag : ∀ i : V, Zlim i i = c - 1 := by
    intro i
    have h1 : Tendsto (fun n => Z (φ n) i i) atTop (𝓝 (Zlim i i)) := hcoord i i
    have hseq : (fun n => Z (φ n) i i) = fun n => u (φ n) - 1 := by
      funext n
      exact hZdiag (φ n) i
    rw [hseq] at h1
    have h2 : Tendsto (fun n => u (φ n) - 1) atTop (𝓝 (c - 1)) :=
      (hu_tendsto.comp hφmono.tendsto_atTop).sub tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- and its entries across edges are `-1`
  have hedge : ∀ i j : V, G.Adj i j → Zlim i j = -1 := by
    intro i j hij
    have h1 : Tendsto (fun n => Z (φ n) i j) atTop (𝓝 (Zlim i j)) := hcoord i j
    have h2 : Tendsto (fun n => Z (φ n) i j) atTop (𝓝 (-1)) := by
      have hseq : (fun n => Z (φ n) i j) = fun _ => (-1 : ℝ) := by
        funext n
        exact hZedge (φ n) i j hij
      rw [hseq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  exact ⟨Zlim, hPSD, hdiag, hedge⟩

/-- The form in which Lemma 4.1 needs it: hypothesis `hZ` of
`Grothendieck.vector_construction_of_theta`. -/
theorem thetaFeasible_thetaComplement' (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) :
    ThetaFeasible G (thetaComplement G) := by
  have hV : Nonempty V := ⟨hne.choose⟩
  haveI := hV
  exact thetaFeasible_thetaComplement_proof G

end Grothendieck

open Grothendieck in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Nonempty V] : ThetaFeasible G (thetaComplement G) :=
  Grothendieck.thetaFeasible_thetaComplement_proof G
