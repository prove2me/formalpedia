-- Prove2me | solution 1 for ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4cde73d5-729e-5f0b-bd4e-8e7bc937784e

import Definitions.Def_ModularCurve_CharPReduction
import Mathlib.FieldTheory.Relrank
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import Theorems.Thm_ModularCurve_StarBank_starBank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve IntermediateField

theorem solution
    (k : Type*) [Field k] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N) :
    (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N := by
  set E := IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) with hE
  have hle : E ≤ modularFunctionFieldC k N :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem k N))
  rw [relfinrank_eq_finrank_of_le hle]

  have hext : extendScalars hle =
      IntermediateField.adjoin E ({jqNModC k N} : Set (LaurentSeries k)) := by
    apply le_antisymm
    ·
      intro x hx
      have hx' : x ∈ modularFunctionFieldC k N := hx
      have hsub : ({jqModC k, jqNModC k N} : Set (LaurentSeries k)) ⊆
          (IntermediateField.adjoin E ({jqNModC k N} : Set (LaurentSeries k)) :
            Set (LaurentSeries k)) := by
        intro y hy
        rcases hy with rfl | hy
        · exact (IntermediateField.adjoin E ({jqNModC k N} : Set (LaurentSeries k))).algebraMap_mem
            (⟨jqModC k, IntermediateField.mem_adjoin_simple_self k (jqModC k)⟩ : E)
        · rcases hy with rfl
          exact IntermediateField.subset_adjoin E _ rfl
      have hres : modularFunctionFieldC k N ≤
          (IntermediateField.adjoin E
              ({jqNModC k N} : Set (LaurentSeries k))).restrictScalars k := by
        exact adjoin_le_iff.mpr hsub
      exact hres hx'
    ·
      exact adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqNModC_mem k N))
  rw [hext]

  refine finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket N ?_
  intro p _ hpN
  have hpℓ : p ≠ ℓ := fun h => hℓN (h ▸ hpN)
  exact StarBank.starBank (ℓ := ℓ) hpℓ

end S_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi (solution)
