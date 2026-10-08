-- Prove2me | solution 1 for NestedLogitVariants.LP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:39:43.146758+00:00
-- url     : https://prove2.me/submissions/c52c7ee5-fe3f-43f5-a0d6-a3942f62ee2f

import Theorems.Thm_NestedLogitVariants_LP_lp3_value_eq
import Theorems.Thm_NestedLogitVariants_LP_lp4_opt_binding
import Theorems.Thm_NestedLogitVariants_LP_lp4_le_optimal

open NestedLogitVariants.LP

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hv0 : 0 < I.v0)
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sh : ι → Finset (Fin n)) (hSmem : ∀ i, Sh i ∈ A i)
    (hSmax : ∀ i, ∀ S ∈ A i,
      nestWeight I i S * (R I i S - xh) ≤ nestWeight I i (Sh i) * (R I i (Sh i) - xh))
    (α β : ℝ) (hfeas : LP3Feasible I (α * xh) (β • yh)) :
    ∀ Sstar, IsOptimal I Sstar →
      revenue I Sstar ≤ α * revenue I Sh ∧ revenue I Sh ≤ revenue I Sstar := by
  intro Sstar hSopt
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    simp [revenue]
  · letI := hι
    by_cases hn : n = 0
    · subst n
      have hempty (S : Finset (Fin 0)) : S = ∅ := by
        ext j
        exact Fin.elim0 j
      simp [revenue, R, hempty]
    · have hb := lp4_opt_binding I hI hv0 A xh yh hopt Sh hSmem hSmax
      constructor
      · have hu := (lp3_value_eq I hI (Nat.pos_of_ne_zero hn) Sstar hSopt).2
          (show α * xh ∈ {x | ∃ y, LP3Feasible I x y} from ⟨β • yh, hfeas⟩)
        rwa [hb.2] at hu
      · have hl := (lp4_le_optimal I hI A xh yh hopt Sstar hSopt).2
        rwa [hb.2] at hl
