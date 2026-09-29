-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isIntegrallyClosed_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8f835299-babc-55c8-a68e-2bb2340eeead

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull"
p2m_open "ModularCurve"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlg adjoin_le_chartAlg chartAlgFin"
p2m_open "ModularCurve.IgusaScheme"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

theorem isIntegrallyClosed_chartAlg (S : Set FN) : IsIntegrallyClosed (chartAlg N ℓ S) := by
  let R : Subalgebra ℤℓ FN := Algebra.adjoin ℤℓ S
  let A : Subalgebra ℤℓ FN := chartAlg N ℓ S
  have hRA : R ≤ A := adjoin_le_chartAlg N ℓ S
  letI : Algebra R A := (Subalgebra.inclusion hRA).toRingHom.toAlgebra
  haveI : IsScalarTower R A FN := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral R A := by
    refine ⟨fun a => ?_⟩
    have ha : IsIntegral R (a : FN) := a.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A FN) Subtype.val_injective).mp ha
  haveI : FaithfulSMul A FN := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Subtype.val_injective
  haveI : IsIntegrallyClosedIn A FN := by
    refine (isIntegrallyClosedIn_iff).mpr ⟨Subtype.val_injective, fun {x} hx => ?_⟩
    have hx' : IsIntegral R x := isIntegral_trans x hx
    exact ⟨⟨x, hx'⟩, rfl⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn_of_faithfulSMul A FN

end IgusaScheme
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin.ModularCurve.IgusaScheme in
theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    IsIntegrallyClosed ↥(chartAlgFin N ℓ) :=
  ModularCurve.IgusaScheme.isIntegrallyClosed_chartAlg N ℓ _

end

end S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_chartAlgFin (solution)
