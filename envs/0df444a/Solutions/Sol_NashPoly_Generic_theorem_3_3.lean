-- Prove2me | solution 1 for NashPoly.Generic.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:21:47.653773+00:00
-- url     : https://prove2.me/submissions/49a41881-15eb-4533-8aee-6b56d290ad90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NashPoly_Generic_Algorithm
import Definitions.Def_NashPoly_Generic_Coef
import Theorems.Thm_NashPoly_Generic_theorem_3_2
import Theorems.Thm_NashPoly_Generic_kkt_points_finite
import Theorems.Thm_NashPoly_Generic_ne_mem_feas
import Theorems.Thm_NashPoly_Generic_feas_exists_min

open MvPolynomial Matrix MeasureTheory NashPoly.Generic

namespace Sol33Aux

/-- Every point of `G` (the feasible set of (3.7)) is a KKT point. -/
theorem gset_sub_kkt {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ)) :
    P.GSet H ⊆ P.KKTSet := by
  intro x hx
  refine ⟨fun i => ⟨(hx i).2.1, (hx i).2.2.2.1⟩, fun i j => P.lam H i x j, fun i => ⟨?_, ?_⟩⟩
  · intro k
    have := (hx i).1 k
    linarith
  · intro j hj
    exact ⟨(hx i).2.2.2.2 j hj, (hx i).2.2.1 j hj⟩

/-- The cut sets of a run consist of feasible strategies. -/
theorem run_cuts_sub {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) {L : ℕ}
    {K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ)} {u : Fin L → Var n → ℝ}
    (hrun : P.IsRun H Θ L K u) : ∀ t : Fin (L + 1), ∀ i, K t i ⊆ P.X i := by
  intro t
  induction t using Fin.induction with
  | zero => intro i; rw [hrun.1 i]; exact Set.empty_subset _
  | succ ℓ ih =>
    intro i
    obtain ⟨U, hU, h1, h2⟩ := (hrun.2 ℓ).2.2.2 i
    rw [hU]
    refine Set.union_subset (ih i) ?_
    by_cases hc : P.CanImprove i (u ℓ)
    · intro v hv; exact ((h1 hc).2 v hv).1
    · rw [h2 hc]; exact Set.empty_subset _

end Sol33Aux

open Sol33Aux in
theorem solution {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)),
      ∀ (E : (i : Fin N) → Finset (Fin (m i)))
        (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ)),
      (∀ i, H i * Gmat ((nepOf c E).g i) = 1) →
      ∀ Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ, Θ.PosDef →
        (∃ B : ℕ,
          (∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
            (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u → L ≤ B) ∧
          ((nepOf c E).Step38Solvable H →
            ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
              (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u →
              ∃ (L' : ℕ) (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
                (u' : Fin L' → Var n → ℝ) (h : L ≤ L'),
                (nepOf c E).RunExtends h K u K' u' ∧
                  (nepOf c E).IsRun H Θ L' K' u' ∧ L' ≤ B ∧
                  (nepOf c E).IsTerminal H Θ (K' (Fin.last L')))) ∧
        ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
          (u : Fin L → Var n → ℝ), (nepOf c E).IsRun H Θ L K u →
          ((nepOf c E).Feas H (K (Fin.last L)) = ∅ → (nepOf c E).NESet = ∅) ∧
          (((nepOf c E).Feas H (K (Fin.last L))).Nonempty →
            ∃ x ∈ (nepOf c E).Feas H (K (Fin.last L)),
              IsMinOn (theta Θ) ((nepOf c E).Feas H (K (Fin.last L))) x) := by
  filter_upwards [kkt_points_finite n m a d ha hd] with c hc
  intro E H hH Θ hΘ
  have hfin : ((nepOf c E).GSet H \ (nepOf c E).NESet).Finite :=
    ((hc E).subset (gset_sub_kkt (nepOf c E) H)).sdiff
  obtain ⟨h1, h2⟩ := theorem_3_2 (nepOf c E) H hH Θ hΘ hfin
  refine ⟨⟨_, h1, h2⟩, ?_⟩
  intro L K u hrun
  constructor
  · intro hempty
    have := ne_mem_feas (nepOf c E) H hH (K (Fin.last L))
      (run_cuts_sub (nepOf c E) H Θ hrun (Fin.last L))
    rw [hempty] at this
    exact Set.subset_empty_iff.mp this
  · intro hne
    exact feas_exists_min (nepOf c E) H _ Θ hΘ hne
