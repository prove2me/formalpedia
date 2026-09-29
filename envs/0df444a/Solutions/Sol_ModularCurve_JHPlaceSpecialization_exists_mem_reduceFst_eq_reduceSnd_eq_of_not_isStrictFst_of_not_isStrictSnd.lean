-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6c26d80d-ccb0-5797-aa4a-0c4169cb3020

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (h₁ : ¬ Psp.IsStrictFst α β hα hβ δ V) (h₂ : ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (hss : Psp.reduceSnd β hβ δ V ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p ∨
      ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V)) :
    ∃ s ∈ SS, Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd β hβ δ V = s.2 := by

  have hcol : Psp.reduceFst α hα V =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ V) := by
    rcases hTD V with h | h
    · exact h
    ·
      have hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) := by
        by_contra hnf
        exact h₁ ⟨h, hnf⟩
      have hfix' : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
          (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V))) =
            Psp.reduceFst α hα V := hfix
      rw [h] at hfix'
      exact hfix'.symm

  have hfix2 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V) := by
    by_contra hnf
    exact h₂ ⟨hcol, hnf⟩
  have hss' : Psp.reduceSnd β hβ δ V ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
    rcases hss with h | h
    · exact h
    · exact absurd hfix2 h

  refine ⟨(qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ V),
    Psp.reduceSnd β hβ δ V), ?_, hcol, rfl⟩
  rw [hSS]
  exact frob_mk_mem_ssNodePairsQExp hss'

end S_ModularCurve_JHPlaceSpecialization_exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd (solution)
