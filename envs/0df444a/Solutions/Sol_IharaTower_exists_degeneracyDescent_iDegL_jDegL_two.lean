-- Prove2me | solution 1 for IharaTower.exists_degeneracyDescent_iDegL_jDegL_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8b68edcd-5cb7-5e3a-b468-b7489e8d58be

import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower IharaTower.CornerData in

theorem solution (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (Hs : Subgroup (ZMod N)ˣ) (Hs' : Subgroup (ZMod (N * q))ˣ)
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [AddCommGroup A] [Module 𝒪 A]
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (H1 N Hs A)] [Module 𝕋' (H1 (N * q) Hs' A)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs A)] [IsScalarTower 𝒪 𝕋' (H1 (N * q) Hs' A)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs A 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) Hs' A 𝕋')
    (hci : ∀ (k : Fin 2) (v : H1 N Hs A), v ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx) →
      ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k v
        ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx))
    (hcj : ∀ (k : Fin 2) (v' : H1 (N * q) Hs' A),
      v' ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx) →
      ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k v'
        ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx))
    (Tq Tl : cd.cornerRing)
    (hTq : ∀ m : cd.cornerModule, ((Tq • m : cd.cornerModule) : H1 N Hs A) = heckeT N Hs q A (m : H1 N Hs A))
    (hTl : ∀ m : cd.cornerModule, ((Tl • m : cd.cornerModule) : H1 N Hs A) = heckeTlower N Hs q A (m : H1 N Hs A)) :
    ∃ D : DegeneracyDescent (𝒪 := 𝒪) cd cd' 2,
      D.iRaw = ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] ∧
      D.jRaw = ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] ∧
      ∀ (k k' : Fin 2) (m : cd.cornerModule), D.jLeg k (D.iLeg k' m) =
        ![![algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' q hq').range.subgroupOf (GammaHUpper N Hs q)).index : 𝒪) * Tq,
            algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' q hq').range.index : 𝒪)],
          ![algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' 1 h1).range.index : 𝒪),
            algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' 1 h1).range.subgroupOf (GammaHLower N Hs q)).index : 𝒪) * Tl]]
          k k' • m := by
  refine ⟨⟨![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'],
    ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1], hci, hcj⟩, rfl, rfl, ?_⟩

  have hnat : ∀ (n : ℕ) (m : cd.cornerModule),
      (((algebraMap 𝒪 cd.cornerRing (n : 𝒪)) • m : cd.cornerModule) : H1 N Hs A) = n • (m : H1 N Hs A) := by
    intro n m
    rw [algebraMap_smul, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
  have hnatT : ∀ (n : ℕ) (T : cd.cornerRing) (m : cd.cornerModule),
      (((algebraMap 𝒪 cd.cornerRing (n : 𝒪) * T) • m : cd.cornerModule) : H1 N Hs A) = n • ((T • m : cd.cornerModule) : H1 N Hs A) := by
    intro n T m
    rw [← smul_smul, hnat]
  intro k k' m
  apply Subtype.ext
  fin_cases k <;> fin_cases k'
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, DegeneracyDescent.jLeg_apply,
      DegeneracyDescent.iLeg_apply, hnatT, hTq]
    change jDeg N (N * q) Hs Hs' q A hq' (iDeg' N (N * q) Hs Hs' 1 A h1 (m : H1 N Hs A)) = _
    rw [CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeT q hq' h1 (dvd_refl _) (one_mul q).symm]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      DegeneracyDescent.jLeg_apply, DegeneracyDescent.iLeg_apply, hnat]
    change jDeg N (N * q) Hs Hs' q A hq' (iDeg' N (N * q) Hs Hs' q A hq' (m : H1 N Hs A)) = _
    rw [CohCarrier.jDeg_comp_iDegP_self hq']
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      DegeneracyDescent.jLeg_apply, DegeneracyDescent.iLeg_apply, hnat]
    change jDeg N (N * q) Hs Hs' 1 A h1 (iDeg' N (N * q) Hs Hs' 1 A h1 (m : H1 N Hs A)) = _
    rw [CohCarrier.jDeg_comp_iDegP_self h1]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      DegeneracyDescent.jLeg_apply, DegeneracyDescent.iLeg_apply, hnatT, hTl]
    change jDeg N (N * q) Hs Hs' 1 A h1 (iDeg' N (N * q) Hs Hs' q A hq' (m : H1 N Hs A)) = _
    rw [CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower hq hqN h1 hq'
      (by push_cast; rw [one_mul]; exact dvd_mul_left _ _) (one_mul q).symm]

end S_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two
end P2MW
export P2MW.S_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two (solution)
