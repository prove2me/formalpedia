-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isCompact_congruenceK1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6dda7850-872d-5bcd-bd23-bbb3f5cd1457

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isCompact_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

open LanglandsTunnell.CubicInduction

namespace CongruenceBottomRow

section BottomRow

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

private def bottomRowConditions (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

private theorem congruenceK1_eq_inter (c : ℕ) :
    LanglandsTunnell.CubicInduction.congruenceK1 R K v c =
      ((LanglandsTunnell.CubicInduction.localMaximalCompact3 R K v :
          Subgroup (GL (Fin 3) (v.adicCompletion K))) : Set (GL (Fin 3) (v.adicCompletion K))) ∩
        bottomRowConditions R K v c :=
  Set.ext fun _ => Iff.rfl

private theorem continuous_entry (i j : Fin 3) :
    Continuous fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) i j :=
  Units.continuous_val.matrix_elem i j

private theorem bottomRowConditions_eq (c : ℕ) :
    bottomRowConditions R K v c =
      (fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ⁻¹'
          {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))} ∩
        ((fun k : GL (Fin 3) (v.adicCompletion K) => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ⁻¹'
            {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))} ∩
          (fun k : GL (Fin 3) (v.adicCompletion K) =>
              (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ⁻¹'
            {y | Valued.v y ≤ WithZero.exp (-(c : ℤ))}) :=
  Set.ext fun _ => Iff.rfl

private theorem isClosed_bottomRowConditions (c : ℕ) : IsClosed (bottomRowConditions R K v c) := by
  obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := K) v c
  have hB : IsClosed {y : v.adicCompletion K | Valued.v y ≤ WithZero.exp (-(c : ℤ))} := by
    rw [← ht]
    exact AdelicLevel.isClosed_setOf_valued_le (K := K) v t ht0
  rw [bottomRowConditions_eq R K v c]
  exact (hB.preimage (continuous_entry R K v 2 0)).inter
    ((hB.preimage (continuous_entry R K v 2 1)).inter
      (hB.preimage ((continuous_entry R K v 2 2).sub continuous_const)))

end BottomRow

end CongruenceBottomRow

open CongruenceBottomRow

theorem solution (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) :
    IsCompact (congruenceK1 (𝓞 ℚ) ℚ v c) := by
  rw [congruenceK1_eq_inter (𝓞 ℚ) ℚ v c]
  exact (isCompact_localMaximalCompact3 v).inter_right (isClosed_bottomRowConditions (𝓞 ℚ) ℚ v c)

end S_LanglandsTunnell_CubicInduction_isCompact_congruenceK1
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isCompact_congruenceK1 (solution)
