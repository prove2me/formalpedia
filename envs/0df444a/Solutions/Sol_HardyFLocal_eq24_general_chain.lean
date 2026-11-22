-- Prove2me | solution 1 for HardyFLocal.eq24_general_chain
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T20:03:51.413859+00:00
-- url     : https://prove2.me/submissions/7103a0b7-c5f0-4b9c-a2a6-876f81873ba2

import Theorems.Thm_HardyFLocal_eq21_pair_expansion
import Theorems.Thm_HardyFLocal_eq25_26_single_vertex

namespace HardyFLocal

private theorem chain_induction (S : FiducialFamily)
    (pairs : ∀ a l, S.map a ∘ₗ S.map l = ∑ k, pairTable S a l k • S.map k)
    (single : ∀ l, S.map l = ∑ k, (Pi.single l 1 : Ω → ℝ) k • S.map k) :
    ∀ ls, compose S ls = ∑ k, chainConst (pairTable S) ls k • S.map k := by
  intro ls
  induction ls with
  | nil => exact S.map_zero.symm.trans (single 0)
  | cons l ls ih =>
    cases ls with
    | nil => simpa [compose, chainConst, chain] using single l
    | cons a as =>
      let u := chainConst (pairTable S) (a :: as)
      change compose S (a :: as) ∘ₗ S.map l =
        ∑ k, (∑ j, u j * pairTable S j l k) • S.map k
      rw [ih]
      change (∑ j, u j • S.map j) ∘ₗ S.map l = _
      apply LinearMap.ext
      intro x
      change (∑ j, u j • S.map j) (S.map l x) = _
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      calc
        ∑ j, u j • S.map j (S.map l x) =
            ∑ j, u j • (∑ k, pairTable S j l k • S.map k) x := by
              apply Finset.sum_congr rfl
              intro j _
              rw [← pairs]
              rfl
        _ = _ := by
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]

private theorem coordinates_unique (S : FiducialFamily) {v : Op (Fin 2)}
    {c d : Ω → ℝ} (hc : v = ∑ k, c k • S.map k) (hd : v = ∑ k, d k • S.map k) : c = d :=
  funext (Fintype.linearIndependent_iffₛ.mp S.linearIndependent c d (hc.symm.trans hd))

private theorem coords_of_expansion (S : FiducialFamily) {v : Op (Fin 2)}
    {c : Ω → ℝ} (h : v = ∑ k, c k • S.map k) : coordsOf S.map v = c := by
  classical
  have ex : ∃ d : Ω → ℝ, v = ∑ k, d k • S.map k := ⟨c, h⟩
  rw [coordsOf, dif_pos ex]
  exact coordinates_unique S ex.choose_spec h

private theorem chain_four (T : PairTable) (w x y z k : Ω) :
    chainConst T [w,x,y,z] k = ∑ a, ∑ b, T z y a * T a x b * T b w k := by
  classical
  simp [chainConst, chain, Pi.single_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

end HardyFLocal

open HardyFLocal

theorem solution (S : FiducialFamily) :
    (∀ l''' l'' l' l k : Ω,
      coordsOf S.map (S.map l''' ∘ₗ S.map l'' ∘ₗ S.map l' ∘ₗ S.map l) k =
        ∑ a, ∑ b, pairTable S l''' l'' a * pairTable S a l' b * pairTable S b l k) ∧
    ∀ ls : List Ω,
      compose S ls = ∑ k, chainConst (pairTable S) ls k • S.map k ∧
      ∀ c : Ω → ℝ, compose S ls = ∑ k, c k • S.map k → c = chainConst (pairTable S) ls := by
  have pairs a l := (eq21_pair_expansion S a l).1
  have single l := (eq25_26_single_vertex S l).1
  have allLists := chain_induction S pairs single
  constructor
  · intro z y x w k
    have eq : S.map z ∘ₗ S.map y ∘ₗ S.map x ∘ₗ S.map w =
        ∑ j, chainConst (pairTable S) [w,x,y,z] j • S.map j := by
      simpa only [compose, LinearMap.id_comp, LinearMap.comp_assoc] using allLists [w,x,y,z]
    exact (congrFun (coords_of_expansion S eq) k).trans (chain_four _ _ _ _ _ _)
  · intro ls
    exact ⟨allLists ls, fun _ h => coordinates_unique S h (allLists ls)⟩
