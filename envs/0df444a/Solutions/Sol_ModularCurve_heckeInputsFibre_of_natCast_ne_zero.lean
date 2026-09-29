-- Prove2me | solution 1 for ModularCurve.heckeInputsFibre_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/cd11bf70-8ccf-5005-86fe-bacebb97c3da

import Theorems.Thm_ModularCurve_heckeDivFibreDescends_of_separable_phi_map
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeInputsFibre_of_natCast_ne_zero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeDivFibreDescends_of_separable_phi_map charLDegeneracyRoof heckeAlphaC heckeBetaC HeckeAlphaCIntegral HeckeBetaCIntegral heckeDivFibre HeckeDivFibreDescends HeckeInputsFibre heckePic0Fibre heckeInputsFibre_intro heckePic0Fibre_eq ModularPolynomialData finiteAlong_heckeAlphaC finiteAlong_heckeBetaC ModularPolynomialData.separable_map_ratFunc_of_prime exists_modularPolynomialData_evalSymm"
p2m_open "ModularCurve"

open AlgebraicCurve

section Closed

variable (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]

private theorem toRingHom_isIntegral_of_finiteAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hfin : FiniteAlong k φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  exact fun x => IsIntegral.of_finite F x

private theorem heckeAlphaCIntegral_of_finite : HeckeAlphaCIntegral k N q :=
  toRingHom_isIntegral_of_finiteAlong k (heckeAlphaC k N q) (finiteAlong_heckeAlphaC k N q)

private theorem heckeBetaCIntegral_of_finite [Fact q.Prime] : HeckeBetaCIntegral k N q :=
  toRingHom_isIntegral_of_finiteAlong k (heckeBetaC k N q) (finiteAlong_heckeBetaC k N q)

private theorem heckeDivFibreDescends_of_natCast_ne_zero [Fact q.Prime] (hqk : (q : k) ≠ 0) :
    HeckeDivFibreDescends k N q := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm q
  exact heckeDivFibreDescends_of_separable_phi_map k N q data hsymm hqk
    (ModularPolynomialData.separable_map_ratFunc_of_prime k q data hqk)

private theorem heckeInputsFibre_of_natCast_ne_zero [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (hqk : (q : k) ≠ 0) : HeckeInputsFibre k N q :=
  heckeInputsFibre_intro k N q (heckeBetaCIntegral_of_finite k N q) (heckeAlphaCIntegral_of_finite k N q)
    (heckeDivFibreDescends_of_natCast_ne_zero k N q hqk ‹_› _ _)

private theorem heckePic0Fibre_eq_of_natCast_ne_zero [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (hqk : (q : k) ≠ 0) :
    heckePic0Fibre k N q
      = (AlgebraicCurve.Divisor.toPic0End
          (heckeDivFibre k N q (heckeBetaCIntegral_of_finite k N q) (heckeAlphaCIntegral_of_finite k N q))).toIntLinearMap :=
  heckePic0Fibre_eq k N q _ _ (heckeDivFibreDescends_of_natCast_ne_zero k N q hqk ‹_› _ _)

end Closed

end ModularCurve

end

#check @ModularCurve.heckeDivFibreDescends_of_natCast_ne_zero
#print axioms ModularCurve.heckeDivFibreDescends_of_natCast_ne_zero
#check @ModularCurve.heckeInputsFibre_of_natCast_ne_zero
#print axioms ModularCurve.heckeInputsFibre_of_natCast_ne_zero
#check @ModularCurve.heckePic0Fibre_eq_of_natCast_ne_zero

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeInputsFibre_of_natCast_ne_zero.ModularCurve AlgebraicCurve in
theorem solution (k : Type*) [Field k] (N q : ℕ) [NeZero N] [NeZero q]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N q)] [Fact q.Prime]
    (hqk : (q : k) ≠ 0) :
    HeckeInputsFibre k N q :=
  ModularCurve.heckeInputsFibre_of_natCast_ne_zero k N q hqk

end S_ModularCurve_heckeInputsFibre_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_heckeInputsFibre_of_natCast_ne_zero (solution)
