-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.weightedHammingSphere_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:03.19774+00:00
-- url     : https://prove2.me/submissions/6e7d6f0a-e0c2-4e47-b406-3f9d98d19f63

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_orderedHammingSphere_card

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (s : ℕ)
    (hsub : s.choose 2 ≤ s * (N - 1))
    (edgeWeight keepWeight expectedVertices neighborWeight : ℝ)
    (hneighbor : neighborWeight = (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
      edgeWeight ^ (s * (N - 1) - s.choose 2))
    (hvertices : expectedVertices = keepWeight * (q : ℝ) ^ N * edgeWeight ^ N.choose 2)
    (hqueries : ∀ x y : Fin N → Fin q, (homQueries x ∪ homQueries y).card =
      N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2) :
    ∑ xy ∈ Finset.univ.filter (fun xy : (Fin N → Fin q) × (Fin N → Fin q) =>
      dHam xy.1 xy.2 = s),
      keepWeight ^ 2 * edgeWeight ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        expectedVertices * keepWeight * neighborWeight := by
  classical
  let sphere := Finset.univ.filter (fun xy : (Fin N → Fin q) × (Fin N → Fin q) =>
    dHam xy.1 xy.2 = s)
  have hcard : sphere.card = q ^ N * (N.choose s * (q - 1) ^ s) :=
    orderedHammingSphere_card s
  have hcongr : ∀ xy ∈ sphere,
      keepWeight ^ 2 * edgeWeight ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        keepWeight ^ 2 * (edgeWeight ^ N.choose 2 *
          edgeWeight ^ (s * (N - 1) - s.choose 2)) := by
    intro xy hxy
    simp only [sphere, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    rw [hqueries xy.1 xy.2, hxy, Nat.add_sub_assoc hsub, pow_add]
  change ∑ xy ∈ sphere, _ = _
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, hcard, hvertices, hneighbor]
  push_cast
  ring
end HighDimSteinerSpanners.Proofs.CSP
