-- Prove2me | solution 1 for Grothendieck.theta_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T04:22:16.67199+00:00
-- url     : https://prove2.me/submissions/1db46bc9-fc35-4c43-b414-6e163e825835

import Mathlib
import Definitions.Def_Grothendieck_Theta

/-!
# `ϑ(G) ≥ 2` for a graph with at least one edge — solution

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs
with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105, proof of Proposition 4.2,
p. 93: "Since `G` has at least one edge, we have `ϑ(G) ≥ 2`".

The theta number is the infimum over the feasible `λ` of the program (4.1),

  `ϑ(G) = min { λ : Z ⪰ 0, Z(u,u) = λ - 1, Z(u,v) = -1 for {u,v} ∈ E }`.

Two facts are needed. First, the program is feasible: the Laplacian matrix of the complete
graph on `V` is positive semidefinite, has diagonal `|V| - 1` and off-diagonal entries `-1`
(the regular simplex of the paper's p. 92), so `λ = |V|` is feasible. Second, every feasible
`λ` satisfies `λ ≥ 2`: positive semidefiniteness gives `Z(u,u) ≥ 0` and, applied to the
two-dimensional subspace spanned by the endpoints of an edge, `Z(u,v)^2 ≤ Z(u,u) Z(v,v)`,
which across an edge reads `1 ≤ (λ-1)^2`.

The file ends with the top-level `theorem solution` of the platform item
`Grothendieck.theta_ge_two`.
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

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
off-diagonal entries are `-1`. This is the regular simplex of p. 92. -/
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

/-- For a graph `G` with at least one edge, the theta number of its complement is at least
`2` (p. 93). -/
theorem theta_ge_two_proof (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) :
    2 ≤ thetaComplement G := by
  classical
  have hmem : {lam : ℝ | ThetaFeasible G lam}.Nonempty := ⟨_, thetaFeasible_card G⟩
  refine le_csInf hmem ?_
  intro lam hlam
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
  by_contra hcon
  push Not at hcon
  nlinarith

end Grothendieck

open Grothendieck in
/-- The platform solution: `ϑ(G) ≥ 2` for a graph with at least one edge. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hne : ∃ u v, G.Adj u v) : 2 ≤ thetaComplement G :=
  Grothendieck.theta_ge_two_proof G hne
