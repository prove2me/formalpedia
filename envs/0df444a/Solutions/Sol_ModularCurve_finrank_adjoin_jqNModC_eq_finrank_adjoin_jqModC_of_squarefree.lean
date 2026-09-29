-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6505d019-2039-5493-8e3c-63fd31383eb0

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_squarefree
import Theorems.Thm_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

namespace H34G2

theorem comap_val_adjoin_simple {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : ↥K) :
    (IntermediateField.adjoin F ({(x : E)} : Set E)).comap K.val = IntermediateField.adjoin F ({x} : Set ↥K) := by
  apply le_antisymm
  · intro k hk
    change K.val k ∈ IntermediateField.adjoin F ({(x : E)} : Set E) at hk
    have hmap : (IntermediateField.adjoin F ({x} : Set ↥K)).map K.val = IntermediateField.adjoin F ({(x : E)} : Set E) := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← hmap, IntermediateField.mem_map] at hk
    obtain ⟨k', hk', hkk'⟩ := hk
    have : k = k' := Subtype.ext (by simpa using hkk'.symm)
    rw [this]; exact hk'
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    change K.val x ∈ IntermediateField.adjoin F ({(x : E)} : Set E)
    exact IntermediateField.mem_adjoin_simple_self F (x : E)

theorem finrank_adjoin_simple_eq_relfinrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (x : ↥K) :
    Module.finrank ↥(IntermediateField.adjoin F ({x} : Set ↥K)) ↥K =
      IntermediateField.relfinrank (IntermediateField.adjoin F ({(x : E)} : Set E)) K := by
  rw [← comap_val_adjoin_simple K x, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

end H34G2

theorem solution
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (hN : Squarefree N) (hN1 : 1 < N)
    (K : IntermediateField L (LaurentSeries L)) (x y : ↥K)
    (hx : (x : LaurentSeries L) = ModularCurve.jqModC L)
    (hy : (y : LaurentSeries L) = ModularCurve.jqNModC L N)
    [FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K] :
    Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K =
      Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K := by
  classical
  set E := LaurentSeries L
  set A : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)) with hA
  set B : IntermediateField L (LaurentSeries L) := IntermediateField.adjoin L ({jqNModC L N} : Set (LaurentSeries L)) with hB
  set M : IntermediateField L (LaurentSeries L) := modularFunctionFieldC L N with hM
  have hAM : A ≤ M := by
    rw [hA, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact jqModC_mem L N
  have hBM : B ≤ M := by
    rw [hB, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact jqNModC_mem L N
  have hMK : M ≤ K := by
    rw [hM, modularFunctionFieldC, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hx ▸ x.2, hy ▸ y.2⟩

  have hxK : Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥K)) ↥K = IntermediateField.relfinrank A K := by
    have h := H34G2.finrank_adjoin_simple_eq_relfinrank K x
    rw [hx] at h
    exact h
  have hyK : Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K = IntermediateField.relfinrank B K := by
    have h := H34G2.finrank_adjoin_simple_eq_relfinrank K y
    rw [hy] at h
    exact h

  have hNL : ((N : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdeg : IntermediateField.relfinrank A M = dedekindPsi N := by
    have h := ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi L N hNL
    have h' := H34G2.finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldFullC L N) ⟨jqModC L, jqModC_mem_full L N⟩
    have h'' : IntermediateField.relfinrank (IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))
        (modularFunctionFieldFullC L N) = dedekindPsi N := h'.symm.trans h
    rw [← ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero L N] at h''
    exact h''

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree N hN hN1
  have hsym := ModularCurve.ModularPolynomialData.evalSymm_of_squarefree N hN hN1 data
  have hdeg' : IntermediateField.relfinrank B M = dedekindPsi N := by
    rw [hB, hM]
    exact ModularCurve.CharPModel.relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm N L data hsym (by rw [← hA, ← hM]; exact hdeg)

  rw [hxK, hyK, ← IntermediateField.relfinrank_mul_relfinrank hAM hMK, ← IntermediateField.relfinrank_mul_relfinrank hBM hMK,
    hdeg, hdeg']

end S_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree (solution)
