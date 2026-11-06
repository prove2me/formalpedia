-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.exists_distinct_slot_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:40.111041+00:00
-- url     : https://prove2.me/submissions/12fd21c2-8597-435a-8ba1-77bcfbcc1e9f

import Definitions.Def_OAI_NumberTheory_DirichletL_Parameters
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersSlotLengths

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp
end OAI.SevenEighths.Parameters
