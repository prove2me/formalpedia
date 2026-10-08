-- Prove2me | solution 1 for Helfgott.residue_series_dirichlet_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T06:48:44.406587+00:00
-- url     : https://prove2.me/submissions/897b5904-7c9b-45b9-ba25-0e287d999495

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Finset
open scoped BigOperators

namespace Helfgott

theorem residue_series_dirichlet_decomposition (q : ℕ) (hq : 0<q)
    (b : ZMod q) (hb : IsUnit b) (c : ℕ → ℂ) (hc : Summable c) :
    (∑' n : ℕ,if (n : ZMod q)=b then c n else 0) =
      (Nat.totient q : ℂ)⁻¹*(∑ χ : DirichletCharacter ℂ q,
        χ b⁻¹*(∑' n : ℕ,χ (n : ZMod q)*c n)) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hf (χ : DirichletCharacter ℂ q) : Summable (fun n : ℕ => χ (n:ZMod q)*c n) := by
    refine hc.norm.of_norm_bounded (f := fun n : ℕ => χ (n:ZMod q)*c n) ?_
    intro n
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hs (χ : DirichletCharacter ℂ q) :
      Summable (fun n : ℕ => χ b⁻¹*(χ (n:ZMod q)*c n)) := (hf χ).mul_left _
  have he (n : ℕ) : (∑ χ : DirichletCharacter ℂ q,χ b⁻¹*(χ (n:ZMod q)*c n)) =
      (Nat.totient q:ℂ)*(if (n:ZMod q)=b then c n else 0) := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb]
    by_cases hn : (n:ZMod q)=b
    · rw [if_pos hn,if_pos hn.symm]
    · rw [if_neg hn,if_neg (Ne.symm hn),zero_mul,mul_zero]
  have hsum : (∑ χ : DirichletCharacter ℂ q,χ b⁻¹*(∑' n : ℕ,χ (n:ZMod q)*c n)) =
      (Nat.totient q:ℂ)*(∑' n : ℕ,if (n:ZMod q)=b then c n else 0) := by
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (s := univ) (fun χ hχ => hs χ)]
    all_goals simp_rw [he]
  rw [hsum,← mul_assoc,inv_mul_cancel₀ hφ,one_mul]

end Helfgott
end

open Finset Helfgott
open scoped BigOperators

theorem solution (q : ℕ) (hq : 0<q)
    (b : ZMod q) (hb : IsUnit b) (c : ℕ → ℂ) (hc : Summable c) :
    (∑' n : ℕ,if (n : ZMod q)=b then c n else 0) =
      (Nat.totient q : ℂ)⁻¹*(∑ χ : DirichletCharacter ℂ q,
        χ b⁻¹*(∑' n : ℕ,χ (n : ZMod q)*c n)) := Helfgott.residue_series_dirichlet_decomposition q hq b hb c hc

#print axioms solution
