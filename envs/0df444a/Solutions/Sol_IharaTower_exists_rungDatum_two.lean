-- Prove2me | solution 1 for IharaTower.exists_rungDatum_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c3e2467e-8cb7-5eee-ac48-f3adcd2295df

import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_jDeg_comp_iDegP_self
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeT
import Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower
import Theorems.Thm_IharaTower_exists_degeneracyDescent_iDegL_jDegL_two
import Theorems.Thm_IharaTower_RungAssembly_deltaComb_two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_exists_rungDatum_two

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CohCarrier IharaLemma _root_.IharaTower IharaTower.CornerData _root_.IharaTower.RungAssembly in

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
    (hTl : ∀ m : cd.cornerModule, ((Tl • m : cd.cornerModule) : H1 N Hs A) = heckeTlower N Hs q A (m : H1 N Hs A))
    (hadj : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B ⟨![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k m', hcj k _ m'.2⟩ m =
        cd'.pairing.B m' ⟨![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k m, hci k _ m.2⟩)
    (a : cd.cornerRing) (res : cd'.cornerRing →ₐ[𝒪] cd.cornerRing) :
    ∃ R : RungDatum (𝒪 := 𝒪) cd.cornerRing cd'.cornerRing cd.cornerModule cd'.cornerModule cd.pairing cd'.pairing,
      R.res = res ∧
      (∀ m : cd.cornerModule, (R.i m : H1 (N * q) Hs' A) =
        iDegL N (N * q) Hs Hs' 1 A 𝒪 h1 ((a • m : cd.cornerModule) : H1 N Hs A) - iDegL N (N * q) Hs Hs' q A 𝒪 hq' m) ∧
      (∀ m' : cd'.cornerModule, (R.j m' : H1 N Hs A) =
        ((a • (⟨jDegL N (N * q) Hs Hs' q A 𝒪 hq' m', hcj 0 _ m'.2⟩ : cd.cornerModule) : cd.cornerModule) : H1 N Hs A)
          - jDegL N (N * q) Hs Hs' 1 A 𝒪 h1 m') ∧
      R.Δ = a ^ 2 * (algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' q hq').range.subgroupOf (GammaHUpper N Hs q)).index : 𝒪) * Tq)
        - a * (algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' q hq').range.index : 𝒪)
            + algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' 1 h1).range.index : 𝒪))
        + algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' 1 h1).range.subgroupOf (GammaHLower N Hs q)).index : 𝒪) * Tl := by
  obtain ⟨D, hDi, hDj, htab⟩ := IharaTower.exists_degeneracyDescent_iDegL_jDegL_two N q hq hqN Hs Hs' h1 hq'
    cd cd' hci hcj Tq Tl hTq hTl
  have hadjL : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m) := by
    intro k m' m
    have hj : D.jLeg k m' = ⟨![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k m', hcj k _ m'.2⟩ :=
      Subtype.ext (by simp [hDj])
    have hi : D.iLeg k m = ⟨![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k m, hci k _ m.2⟩ :=
      Subtype.ext (by simp [hDi])
    rw [hj, hi]
    exact hadj k m' m
  let L := D.toLegDatum _ hadjL htab
  refine ⟨rungDatumOfLegs L ![a, -1] res, rfl, ?_, ?_, ?_⟩
  · intro m
    have hi0 : ∀ v : cd.cornerModule, (D.iLeg 0 v : H1 (N * q) Hs' A) = iDegL N (N * q) Hs Hs' 1 A 𝒪 h1 v := fun v => by
      simp [hDi]
    have hi1 : ∀ v : cd.cornerModule, (D.iLeg 1 v : H1 (N * q) Hs' A) = iDegL N (N * q) Hs Hs' q A 𝒪 hq' v := fun v => by
      simp [hDi]
    simp only [rungDatumOfLegs_i, iComb, Fin.sum_univ_two, Fin.isValue, LinearMap.add_apply, LinearMap.comp_apply,
      smulLinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Submodule.coe_add,
      neg_smul, one_smul, Submodule.coe_neg, map_neg, sub_eq_add_neg]
    rw [show L.iLeg = D.iLeg from rfl, hi0, hi1]
  · intro m'
    have hj0 : D.jLeg 0 m' = ⟨jDegL N (N * q) Hs Hs' q A 𝒪 hq' m', hcj 0 _ m'.2⟩ :=
      Subtype.ext (by simp [hDj])
    have hj1 : (D.jLeg 1 m' : H1 N Hs A) = jDegL N (N * q) Hs Hs' 1 A 𝒪 h1 m' := by simp [hDj]
    simp only [rungDatumOfLegs_j, jComb, Fin.sum_univ_two, Fin.isValue, LinearMap.add_apply, LinearMap.comp_apply,
      smulLinear_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Submodule.coe_add,
      neg_smul, one_smul, Submodule.coe_neg, sub_eq_add_neg]
    rw [show L.jLeg = D.jLeg from rfl, hj0, hj1]
  · rw [rungDatumOfLegs_Δ, deltaComb_two L _ _ _ _ (DegeneracyDescent.toLegDatum_table _ _ _ _) ![a, -1]]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

namespace IharaTower p2m_export "IharaTower" "CornerData DegeneracyDescent DegeneracyDescent.toLegDatum_table H1CornerData RungDatum exists_degeneracyDescent_iDegL_jDegL_two" namespace RungAssembly p2m_export "IharaTower.RungAssembly" "smulLinear_apply iComb jComb rungDatumOfLegs rungDatumOfLegs_i rungDatumOfLegs_j rungDatumOfLegs_Δ deltaComb_two" end IharaTower.RungAssembly
p2m_open_scoped "IharaTower IharaTower.RungAssembly" in

theorem IharaTower.RungAssembly.map_delta_two_general {𝒪 : Type} [CommRing 𝒪] {T : Type} [CommRing T] [Algebra 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (Tq Tl a : T) (q nu nl nq n1 : ℕ) (b : 𝒪)
    (hnu : nu = 1) (hnl : nl = 1) (hnq : nq = q + 1) (hn1 : n1 = q + 1)
    (hT : πT Tq = πT a + b) (hl : πT Tl = πT Tq) (hab : πT a * b = q) :
    πT (a ^ 2 * (algebraMap 𝒪 T (nu : 𝒪) * Tq) - a * (algebraMap 𝒪 T (nq : 𝒪) + algebraMap 𝒪 T (n1 : 𝒪))
        + algebraMap 𝒪 T (nl : 𝒪) * Tl) = (πT a - b) * (πT a ^ 2 - 1) := by
  subst hnu hnl hnq hn1
  simp only [map_sub, map_mul, map_add, map_pow, AlgHom.commutes, map_natCast, Nat.cast_one, Nat.cast_add,
    Algebra.algebraMap_self, RingHom.id_apply, map_one, hl, hT]
  linear_combination (2 * πT a) * hab

end S_IharaTower_exists_rungDatum_two
end P2MW
export P2MW.S_IharaTower_exists_rungDatum_two (solution)
