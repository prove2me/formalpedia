-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.polynomial_indexed_computability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:12.702191+00:00
-- url     : https://prove2.me/submissions/993cda00-ee86-41c5-b12c-c04c8c20eafd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_vector_program
import Theorems.Thm_ITPIRPreproc_MatchVec_WordRAM_indexed_table_of_vector_program
import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
import Mathlib.Tactic

open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction

theorem solution :
    ∃ (dim : ℕ → ℕ)
      (rows : ∀ h : ℕ, Fin (2^h) ↪ (Fin (wordLength h) → Fin (wordLength h)))
      (coords : ∀ h : ℕ, Fin (dim h) ≃
        Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h)))
      (C₀ : ℝ) (c₀ : ℕ) (vecProg tableProg : WordRAM.Program),
      MVComputable dim
        (fun h r j => leftVector (coefficient (wordLength h) (exponent2 h) (exponent3 h))
          (rows h r) (coords h j))
        (fun h r j => rightVector (rows h r) (coords h j))
        C₀ c₀ vecProg tableProg := by
  rcases polynomial_vector_program with
    ⟨dim, rows, coords, C₀, c₀, vecProg, hvec⟩
  let u : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6 :=
    fun h r j => leftVector (coefficient (wordLength h) (exponent2 h) (exponent3 h))
      (rows h r) (coords h j)
  let v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6 :=
    fun h r j => rightVector (rows h r) (coords h j)
  have hvec' : IndexedVectorComputable dim u v C₀ c₀ vecProg := hvec
  rcases WordRAM.indexed_table_of_vector_program dim u v C₀ c₀ vecProg hvec' with
    ⟨tableProg, htabdet, htab⟩
  refine ⟨dim, rows, coords, C₀ + 20, c₀ + 4, vecProg, tableProg,
    hvec.1, htabdet, ?_⟩
  intro h hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  have hp : (h : ℝ) ^ c₀ ≤ (h : ℝ) ^ (c₀ + 4) :=
    pow_le_pow_right₀ hh1 (by omega)
  have hCd : 0 ≤ C₀ * dim h := by
    let a₀ : Fin (2 ^ h) := ⟨0, by positivity⟩
    exact (Nat.cast_nonneg _).trans (hvec.2 h hh a₀).2.2.2
  have hcoef : C₀ * dim h ≤ (C₀ + 20) * dim h := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (dim h)]
  constructor
  · intro a
    refine ⟨(hvec.2 h hh a).1, (hvec.2 h hh a).2.1, ?_⟩
    calc
      (WordRAM.cost vecProg (encNat h ++ encNat a.val) WordRAM.zeroTape : ℝ)
          ≤ C₀ * dim h * (h : ℝ) ^ c₀ := (hvec.2 h hh a).2.2.1
      _ ≤ C₀ * dim h * (h : ℝ) ^ (c₀ + 4) :=
        mul_le_mul_of_nonneg_left hp hCd
      _ ≤ (C₀ + 20) * dim h * (h : ℝ) ^ (c₀ + 4) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  · exact htab h hh
