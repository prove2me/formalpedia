-- Prove2me | solution 1 for KoanaKPaths.Main.graphLayer_natAbs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:51.744203+00:00
-- url     : https://prove2.me/submissions/db48ec3e-f3b8-4409-bc82-0d84ce07bd08

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 400000
open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates




























lemma wedge_finset {k : ℕ} (A : Coordinates k) (v : Fin k → ℤ) (S : Finset (Fin k)) :
    wedgeRight A v S = ∑ r ∈ S,
      (-1 : ℤ)^(S.card-1+S.sort.idxOf r)*A (S.erase r)*v r := by
  unfold wedgeRight
  have h := Finset.sum_coe_sort (M := ℤ) S (fun r : Fin k =>
    (-1 : ℤ)^(S.card-1+S.sort.idxOf r)*A (S.erase r)*v r)
  convert h using 1 <;> rfl







































end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma natAbs_sum_le {α : Type} (s : Finset α) (f : α→ℤ) :
    (∑ x∈s, f x).natAbs ≤ ∑ x∈s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma sgn_natAbs (b : Bool) : (sgn b).natAbs=1 := by cases b <;> norm_num [sgn]

lemma wedge_natAbs_bound {k : ℕ} (A : Coordinates k) (v : Fin k→ℤ) (B : ℕ)
    (hA : ∀ S, (A S).natAbs≤B) (hv : ∀ r, (v r).natAbs=1) (S : Finset (Fin k)) :
    (wedgeRight A v S).natAbs≤k*B := by
  let f : Fin k→ℤ := fun r => (-1 : ℤ)^(S.card-1+S.sort.idxOf r)*A (S.erase r)*v r
  have hsum : wedgeRight A v S=∑ r∈S, f r := by
    have h := wedge_finset A v S
    convert h using 1 <;> rfl
  rw [hsum]
  calc
    _ ≤ ∑ r∈S, (f r).natAbs := natAbs_sum_le S f
    _ ≤ ∑ _r∈S, B := by
      apply Finset.sum_le_sum
      intro r hr
      dsimp only [f]
      simpa only [Int.natAbs_mul,Int.natAbs_pow,show Int.natAbs (-1)=1 from rfl,one_pow,
        one_mul,hv r,mul_one] using hA (S.erase r)
    _ = S.card*B := by simp
    _ ≤ k*B := Nat.mul_le_mul_right B (by simpa using S.card_le_univ)



lemma graphLayer_natAbs {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) (S : Finset (Fin k)) :
    (graphLayer arcs σ R p v a S).natAbs ≤ (layerRadius n k ℓ)^p := by
  induction p using Nat.twoStepInduction generalizing v a S with
  | zero => simp [graphLayer]
  | one =>
    have hu : ∀ T, (unit k T).natAbs≤1 := by intro T; unfold unit; split <;> norm_num
    have hw := wedge_natAbs_bound (unit k) (fun r => sgn (σ v r)) 1 hu (fun r => sgn_natAbs _) S
    have hk : k≤layerRadius n k ℓ := by
      have hh := Nat.mul_le_mul_left k (by omega : 1≤n*ℓ+1)
      unfold layerRadius
      nlinarith
    have hw' : (wedgeRight (unit k) (fun r => sgn (σ v r)) S).natAbs≤k := by simpa using hw
    simpa [graphLayer,wordCoordinates,Int.natAbs_mul,sgn_natAbs] using le_trans hw' hk
  | more i ih0 ih =>
    rw [graphLayer]
    split_ifs with hi
    · let A : Coordinates k := ∑ u : Fin n, if (u,v)∈arcs.toFinset then
        ∑ b : Fin ℓ, sgn (R.2 ⟨i,hi⟩ a (b,v)) • graphLayer arcs σ R (i+1) u b else 0
      have hA : ∀ T, (A T).natAbs≤n*ℓ*(layerRadius n k ℓ)^(i+1) := by
        intro T
        dsimp only [A]
        rw [Finset.sum_apply]
        calc
          _ ≤ ∑ u : Fin n, ((if (u,v)∈arcs.toFinset then
              ∑ b : Fin ℓ, sgn (R.2 ⟨i,hi⟩ a (b,v)) • graphLayer arcs σ R (i+1) u b else 0) T).natAbs :=
            natAbs_sum_le Finset.univ _
          _ ≤ ∑ _u : Fin n, ℓ*(layerRadius n k ℓ)^(i+1) := by
            apply Finset.sum_le_sum
            intro u _
            by_cases ha : (u,v)∈arcs
            · have haF : (u,v)∈arcs.toFinset := by simpa using ha
              simp only [if_pos haF,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
              calc
                _ ≤ ∑ b : Fin ℓ, (sgn (R.2 ⟨i,hi⟩ a (b,v))*graphLayer arcs σ R (i+1) u b T).natAbs :=
                  natAbs_sum_le Finset.univ _
                _ ≤ ∑ _b : Fin ℓ, (layerRadius n k ℓ)^(i+1) := by
                  apply Finset.sum_le_sum
                  intro b _
                  simpa only [Int.natAbs_mul,sgn_natAbs,one_mul] using ih u b T
                _ = _ := by simp
            · simp [ha]
          _ = _ := by simp; ring
      have hw := wedge_natAbs_bound A (fun r => sgn (σ v r))
        (n*ℓ*(layerRadius n k ℓ)^(i+1)) hA (fun r => sgn_natAbs _) S
      calc
        _ ≤ k*(n*ℓ*(layerRadius n k ℓ)^(i+1)) := hw
        _ = (k*n*ℓ)*(layerRadius n k ℓ)^(i+1) := by ring
        _ ≤ (layerRadius n k ℓ)*(layerRadius n k ℓ)^(i+1) :=
          Nat.mul_le_mul_right _ (by
            have hh := Nat.mul_le_mul_left k (Nat.le_succ (n*ℓ))
            unfold layerRadius
            nlinarith)
        _ = (layerRadius n k ℓ)^(i+2) := by ring
    · simp










end KoanaKPaths.Main

end

theorem solution :
∀ {n k ℓ : Nat} (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (σ : KoanaKPaths.Main.Labels n k)
  (R : KoanaKPaths.Main.SketchSigns n k ℓ) (p : Nat) (v : Fin n) (a : Fin ℓ) (S : Finset.{0} (Fin k)),
  @LE.le.{0} Nat instLENat (Int.natAbs (@KoanaKPaths.Main.graphLayer n k ℓ arcs σ R p v a S))
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (KoanaKPaths.Main.layerRadius n k ℓ) p) := by
  exact @KoanaKPaths.Main.graphLayer_natAbs
