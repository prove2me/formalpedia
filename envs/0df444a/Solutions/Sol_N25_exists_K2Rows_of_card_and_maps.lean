-- Prove2me | solution 1 for N25.exists_K2Rows_of_card_and_maps
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:12.475447+00:00
-- url     : https://prove2.me/submissions/f6d6f83c-8a7e-4e42-8935-b3eb25edceb6

import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_exists_psi_ne_cyclotomic
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false

noncomputable section

namespace N25

local instance prime71_N25_exists_K2Rows_of_card_and_maps_sba3708 : Fact (Nat.Prime 71) :=
  ⟨by decide⟩

/-- On a kernel of order seventy-one squared, the two prescribed character maps
are exact: their composite vanishes because the characters differ, and their
kernel and image then have the same cardinality. -/
theorem _root_.solution (hcard : Nat.card ↥V = 71 ^ 2)
    (i : ZMod 71 →+ ↥V) (hi : Function.Injective i)
    (hiGal : ∀ (σ : Gal) (t : ZMod 71), vAct σ (i t) = i ((psi σ : ZMod 71) * t))
    (q : ↥V →+ ZMod 71) (hq : Function.Surjective q)
    (hqGal : ∀ (σ : Gal) (v : ↥V), q (vAct σ v) =
      (ExtCitation.cycloChar 71 σ : ZMod 71) * q v) : Nonempty K2Rows := by
  classical
  let : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hzero (t : ZMod 71) : q (i t) = 0 := by
    obtain ⟨σ, hσ⟩ := exists_psi_ne_cyclotomic
    have he := hqGal σ (i t)
    rw [hiGal] at he
    have hm := ZMod.map_smul (q.comp i) (psi σ : ZMod 71) t
    change q (i ((psi σ : ZMod 71) * t)) = (psi σ : ZMod 71) * q (i t) at hm
    rw [hm] at he
    have hz : ((psi σ : ZMod 71) - (ExtCitation.cycloChar 71 σ : ZMod 71)) *
        q (i t) = 0 := by rw [sub_mul, he, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hσ)
  have hle : i.range ≤ q.ker := by
    rintro v ⟨t, rfl⟩
    exact hzero t
  have hiCard : Nat.card i.range = 71 := by
    calc
      Nat.card i.range = Nat.card (ZMod 71) :=
        (Nat.card_congr (Equiv.ofInjective i hi)).symm
      _ = 71 := by simp
  have hqCard : Nat.card q.range = 71 := by
    rw [AddMonoidHom.range_eq_top.mpr hq]
    simp
  have hkCard : Nat.card q.ker = 71 := by
    have hm := q.ker.card_mul_index
    rw [AddSubgroup.index_ker, hqCard, hcard] at hm
    omega
  have hex : i.range = q.ker := by
    apply SetLike.ext'
    apply Set.eq_of_subset_of_ncard_le hle
    change Nat.card q.ker ≤ Nat.card i.range
    rw [hiCard, hkCard]
  exact ⟨{
    i := i
    q := q
    i_injective := hi
    exact_at_V := hex.symm
    q_surjective := hq
    i_galois := hiGal
    q_galois := hqGal }⟩

end N25
