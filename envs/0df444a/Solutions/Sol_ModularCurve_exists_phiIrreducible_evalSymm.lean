-- Prove2me | solution 1 for ModularCurve.exists_phiIrreducible_evalSymm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d69154cc-2187-5d53-8545-df3b03f29595

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_PhiGen_exists_phiGenDescends
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
import Theorems.Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
import Theorems.Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq
import Theorems.Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq
import Theorems.Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq
import Theorems.Thm_ModularCurve_PhiGen_phiIrreducible_of_splits
import Mathlib.NumberTheory.Cyclotomic.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_phiIrreducible_evalSymm
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "jq ModularPolynomialData EvalSymm PhiIrreducible PhiGen.IntCoeffs PhiGen.exists_phiGenDescends PhiGen.mem_adjoin_jq_of_phiGenDescends PhiGen.exists_modularPolynomialData_coeff_eq PhiGen.evalSymm_of_coeff_evalAtJ_eq PhiGen.splits_of_coeff_evalAtJ_eq PhiGen.phiIrreducible_of_splits"
p2m_open "ModularCurve"

private theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by

  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ

  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k

  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨data,
    PhiGen.phiIrreducible_of_splits ℓ hzu.unit hζ data (PhiGen.splits_of_coeff_evalAtJ_eq hzu.unit hc data hcoeff),
    PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_phiIrreducible_evalSymm.ModularCurve ModularCurve.PhiGen in

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ :=
  ModularCurve.exists_phiIrreducible_evalSymm ℓ

#print axioms solution

end S_ModularCurve_exists_phiIrreducible_evalSymm
end P2MW
export P2MW.S_ModularCurve_exists_phiIrreducible_evalSymm (solution)
