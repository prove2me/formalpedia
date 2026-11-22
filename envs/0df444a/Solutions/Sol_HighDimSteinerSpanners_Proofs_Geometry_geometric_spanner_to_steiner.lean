-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Geometry.geometric_spanner_to_steiner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:59.105909+00:00
-- url     : https://prove2.me/submissions/dc3bfd09-4d48-4877-9745-67532692fa5e

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Geometry
noncomputable section
private lemma lpDist_nonneg {p : ℝ} {d : ℕ} (x y : Fin d → ℝ) :
    0 ≤ lpDist p x y := by
  unfold lpDist
  positivity
end
end HighDimSteinerSpanners.Proofs.Geometry
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Geometry
noncomputable section
namespace HighDimSteinerSpanners.Proofs.Geometry
theorem _root_.solution
    (h_lp : ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y))
    {p : ℝ} (hp : 1 ≤ p) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) (hGeom : IsGeometricSpanner p P C G) :
    ∃ (H : SimpleGraph (Fin n ⊕ PEmpty)) (w : Sym2 (Fin n ⊕ PEmpty) → ℝ),
      IsNonMetricSteinerSpanner p P C H w ∧
      (Nat.card H.edgeSet : ℝ) ≤ (Nat.card G.edgeSet : ℝ) := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let proj : Fin n ⊕ PEmpty → Fin n := Sum.elim id PEmpty.elim
  let wG : Sym2 (Fin n) → ℝ :=
    Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
      simp only [lpDist, abs_sub_comm]⟩
  let H : SimpleGraph (Fin n ⊕ PEmpty) :=
    { Adj := fun x y => G.Adj (proj x) (proj y)
      symm := ⟨fun _ _ h => G.adj_symm h⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  let w : Sym2 (Fin n ⊕ PEmpty) → ℝ := fun e => wG (Sym2.map proj e)
  refine ⟨H, w, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro e _
      revert e
      refine Sym2.ind (fun x y _ => ?_)
      simpa [w, wG] using lpDist_nonneg (P (proj x)) (P (proj y))
    · intro i j
      have hwalk_lb : ∀ {u v : Fin n ⊕ PEmpty} (q : H.Walk u v),
          lpDist p (P (proj u)) (P (proj v)) ≤ walkWeight w q := by
        intro u v q
        induction q with
        | @nil u =>
          simp [walkWeight, h_lp p hp]
        | @cons u b v _ q' ih =>
          have htri : lpDist p (P (proj u)) (P (proj v)) ≤
              lpDist p (P (proj u)) (P (proj b)) + lpDist p (P (proj b)) (P (proj v)) := by
            simp only [h_lp p hp]
            exact dist_triangle _ _ _
          have hw_eq : w s(u, b) = lpDist p (P (proj u)) (P (proj b)) := by
            simp [w, wG]
          simp only [walkWeight, hw_eq]
          linarith
      exact le_iInf (fun q => ENNReal.ofReal_le_ofReal (hwalk_lb q))
    · intro i j
      let emb : G →g H := ⟨Sum.inl, fun h => h⟩
      have hww_map : ∀ {u v : Fin n} (q : G.Walk u v),
          walkWeight w (q.map emb) = walkWeight wG q := by
        intro u v q
        induction q with
        | nil => simp [walkWeight]
        | @cons u b v _ q' ih =>
          simp only [SimpleGraph.Walk.map_cons, walkWeight, ih]
          rfl
      have hle_gd : graphDist H w (.inl i) (.inl j) ≤ graphDist G wG i j := by
        unfold graphDist
        refine le_iInf (fun q => ?_)
        calc
          (⨅ p_w : H.Walk (.inl i) (.inl j), ENNReal.ofReal (walkWeight w p_w))
            ≤ ENNReal.ofReal (walkWeight w (q.map emb)) := iInf_le _ (q.map emb)
          _ = ENNReal.ofReal (walkWeight wG q) := by rw [hww_map]
      exact le_trans hle_gd (hGeom i j)
  · have hproj_inj : Function.Injective proj := by
      rintro (u | s) (v | s) h
      · exact congrArg Sum.inl h
      · exact PEmpty.elim s
      · exact PEmpty.elim s
      · exact PEmpty.elim s
    let f_edge : H.edgeSet → G.edgeSet := fun e =>
      ⟨Sym2.map proj e.1, by
        rcases e with ⟨s, hs⟩
        revert hs
        refine Sym2.ind (fun x y hs => ?_) s
        simpa [SimpleGraph.mem_edgeSet] using hs⟩
    have hf_inj : Function.Injective f_edge := by
      intro e₁ e₂ heq
      apply Subtype.ext
      exact Sym2.map.injective hproj_inj (Subtype.mk.inj heq)
    have hnat : Nat.card H.edgeSet ≤ Nat.card G.edgeSet :=
      Nat.card_le_card_of_injective f_edge hf_inj
    exact_mod_cast hnat
end HighDimSteinerSpanners.Proofs.Geometry
