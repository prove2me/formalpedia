-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.inv_mem_congruenceK1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2e39b569-d120-5bf1-848d-fc701a793fe1

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_inv_mem_congruenceK1

set_option autoImplicit false

open Matrix IsDedekindDomain
open LanglandsTunnell.CubicInduction

namespace CongruenceBottomEntries

private theorem mem_congruenceK1_iff_bottom_sub_one (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (c : ℕ) (k : GL (Fin 3) (v.adicCompletion K)) :
    k ∈ congruenceK1 R K v c ↔
      k ∈ localMaximalCompact3 R K v ∧
        ∀ l : Fin 3,
          Valued.v (((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1) 2 l) ≤ WithZero.exp (-(c : ℤ)) := by
  rw [mem_congruenceK1_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨h0, ?_⟩
    intro l
    fin_cases l
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h1
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h2
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h3
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_, ?_, ?_⟩
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 0
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 1
    · simpa [Matrix.sub_apply, Matrix.one_apply] using h 2

end CongruenceBottomEntries

open CongruenceBottomEntries

theorem solution
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) {c : ℕ}
    {k : GL (Fin 3) (v.adicCompletion K)} (hk : k ∈ congruenceK1 R K v c) :
    k⁻¹ ∈ congruenceK1 R K v c := by
  obtain ⟨hk0, hk1⟩ := (mem_congruenceK1_iff_bottom_sub_one R K v c k).1 hk
  refine (mem_congruenceK1_iff_bottom_sub_one R K v c k⁻¹).2 ⟨inv_mem hk0, fun l => ?_⟩
  have hsplit : ((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) - 1 =
      (1 - (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))) *
        ((k⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) := by
    rw [sub_mul, one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hsplit]
  refine valued_mul_apply_le3 R K v (fun m => ?_) (fun m => hk0.2 m l)
  rw [← neg_sub, Matrix.neg_apply, Valuation.map_neg]
  exact hk1 m

end S_LanglandsTunnell_CubicInduction_inv_mem_congruenceK1
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_inv_mem_congruenceK1 (solution)
