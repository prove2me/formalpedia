-- Prove2me | solution 1 for MonoSkew.Main.proposition_2_7_iv
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-23T12:39:58.437971+00:00
-- url     : https://prove2.me/submissions/fcb82a6f-67ce-4b92-ada7-a9910d7f6557

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_MonoSkew_Main_Basic

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

open MonoSkew.Main

/-- Proposition 2.7(iv) (p. 8): for every `γ > 0`,
`J_{γM}(x, v) = (J_{γA}(x + γz), J_{γB⁻¹}(v − γr))`, stated as: if `JA` is the resolvent of
`γA` and `JBi` the resolvent of `γB⁻¹`, then the map
`(x, v) ↦ (JA(x + γz), JBi(v − γr))` is the resolvent of `γM`. -/
theorem solution {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H → Set H) (B : G → Set G) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (L : H →L[ℝ] G) (z : H) (r : G)
    (γ : ℝ) (hγ : 0 < γ) (JA : H → H) (hJA : IsResolvent γ A JA)
    (JBi : G → G) (hJBi : IsResolvent γ (opInv B) JBi) :
    IsResolvent γ (opM A B z r)
      (fun p : K H G => WithLp.toLp 2 (JA (p.fst + γ • z), JBi (p.snd - γ • r))) := by
  intro p
  constructor
  · change γ⁻¹ • (p.fst - JA (p.fst + γ • z)) + z ∈ A (JA (p.fst + γ • z))
    have h := hJA (p.fst + γ • z)
    convert h using 1 <;> (simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]; abel)
  · change γ⁻¹ • (p.snd - JBi (p.snd - γ • r)) - r ∈ opInv B (JBi (p.snd - γ • r))
    have h := hJBi (p.snd - γ • r)
    convert h using 1 <;> (simp only [smul_sub, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]; abel)


