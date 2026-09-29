-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_outer_hash_budget_of_degree_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:23:35.083962+00:00
-- url     : https://prove2.me/submissions/97266ce0-e604-4af7-a82a-1a596b688048

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_MME_StothersFourth_fixedHash_budget_of_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_behrend_margin_parameters

open MME BigOperators Filter Topology

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

noncomputable section

private theorem fixedHashAllTargetEdges_card_eq_natCard (m : ℕ) :
    (fixedHashAllTargetEdges m).card =
      Nat.card
        {a : FixedMarginalSupportedAddress m //
          FixedHasExactJointProfile a} := by
  classical
  let : Fintype (FixedOuterAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (fixedOuterLength m) → Fin 9))
  let : Fintype (FixedMarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : FixedOuterAddress m //
        FixedCoordinatewiseSupported a ∧ FixedMarginallyRegular a})
  let : Fintype
      {a : FixedMarginalSupportedAddress m //
        FixedHasExactJointProfile a} := by
    infer_instance
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem fixedHashStar_card_eq_natCard
    (m : ℕ) (i : Fin 3) (a : FixedMarginalSupportedAddress m) :
    ((fixedHashMarginalUniverse m).filter
        (fun b ↦ b.1 i = a.1 i)).card =
      Nat.card
        {b : FixedMarginalSupportedAddress m // b.1 i = a.1 i} := by
  classical
  let : Fintype (FixedOuterAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (fixedOuterLength m) → Fin 9))
  let : Fintype (FixedMarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {b : FixedOuterAddress m //
        FixedCoordinatewiseSupported b ∧ FixedMarginallyRegular b})
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (hdata : ∀ᶠ m : ℕ in atTop,
      let N := fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ)
      let Dstar : ℕ :=
        (∏ j : Fin 9, (fixedMarginalCount m j).factorial) /
          ∏ sigma : {sigma : Fin 3 → Fin 9 //
              (∑ s, (sigma s).val) = 8},
            (fixedJointMultiplicity m sigma.1).factorial
      let P := (6 * (N + 1)) ^ 100
      let D := P * Dstar
      (Nat.card
          {a : FixedMarginalSupportedAddress m //
            FixedHasExactJointProfile a} : ℝ) = V * (Dstar : ℝ) ∧
        1 ≤ Dstar ∧
        (∀ i : Fin 3,
          ∀ a : {a : FixedMarginalSupportedAddress m //
            FixedHasExactJointProfile a},
          Nat.card
            {b : FixedMarginalSupportedAddress m //
              b.1 i = a.1.1 i} ≤ D) ∧
        D ≤ 5 ^ (1000 * N)) :
    ∀ᶠ m : ℕ in atTop,
      let N := fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ)
      ∃ E : Finset (FixedMarginalSupportedAddress m),
        FixedMarginalVertexClosed E ∧
        ((fixedTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((fixedExactTargetEdges E).card : ℝ) := by
  filter_upwards [hdata, eventually_gt_atTop 0] with m hmdata hm
  dsimp only at hmdata
  let N : ℕ := fixedOuterLength m
  let V : ℝ :=
    (N.factorial : ℝ) /
      ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ)
  let Dstar : ℕ := fixedHashTargetStarDegree m
  let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
  rcases hmdata with ⟨hTcard, hDstar, hdegreeCard, hD5⟩
  have hT : ((fixedHashAllTargetEdges m).card : ℝ) =
      V * (Dstar : ℝ) := by
    rw [fixedHashAllTargetEdges_card_eq_natCard]
    simpa only [V, Dstar, fixedHashTargetStarDegree,
      fixedHashTargetJointTable] using hTcard
  have hdeg : ∀ i : Fin 3, ∀ a ∈ fixedHashAllTargetEdges m,
      ((fixedHashMarginalUniverse m).filter
        (fun b ↦ b.1 i = a.1 i)).card ≤ D := by
    intro i a ha
    rw [fixedHashStar_card_eq_natCard]
    apply hdegreeCard i
      (⟨a, ?_⟩ : {a : FixedMarginalSupportedAddress m //
        FixedHasExactJointProfile a})
    simpa only [fixedHashAllTargetEdges, fixedHashMarginalUniverse,
      fixedExactTargetEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using ha
  obtain ⟨p, hpPrime, hp9, hpOdd, S, hSrange, hSfree, hmargin⟩ :=
    mme_stothers_fixed_behrend_margin_parameters N Dstar hDstar
      (by simpa only [N, Dstar, D, fixedHashTargetStarDegree,
          fixedHashTargetJointTable] using hD5)
  let : Fact p.Prime := ⟨hpPrime⟩
  have hV : 0 ≤ V := by
    dsimp only [V]
    positivity
  simpa only [N, V] using
    fixedHash_budget_of_degree m p D Dstar hm hp9 hpOdd S hSrange hSfree
      V
      (Real.exp
        (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))))
      hV hT hdeg
      (by simpa only [D] using hmargin)
