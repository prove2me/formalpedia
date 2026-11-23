-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.975922+00:00
-- url     : https://prove2.me/submissions/d5f302d2-b550-4135-a54e-2d984070b22b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Theorems.Thm_GlobalTheory_CuspGL_mangoldtConv_eq_of_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ f ^ m = g ^ k} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hg', k, hk, h⟩
      exact mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := m) (h ▸ dvd_pow_self g hk.ne')
    · rintro rfl
      exact ⟨hf, hf', m, hm, rfl⟩
  rw [mangoldt, this, finsum_mem_singleton]
end GlobalTheory.CuspGL
