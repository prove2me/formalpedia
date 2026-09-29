-- Prove2me | solution 1 for NumberField.SUnits.moduleFinite_sUnitsRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8abe5438-7ddd-5a98-8e2b-db260aa0ada7

import Mathlib
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_M4aHerbrand_finrank_sUnit_eq
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_moduleFinite_sUnitsRep

set_option autoImplicit false
p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_SUnits_moduleFinite_sUnitsRep.NumberField"

namespace NumberField
p2m_export "NumberField" "SUnits.placesAbove SUnits.mem_placesAbove SUnits.sUnits SUnits.sUnitsSubmodule SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep SUnits.val SUnits.val_mem SUnits.sUnits_eq_unit"
namespace SUnits
p2m_export "NumberField.SUnits" "placesAbove mem_placesAbove sUnits sUnitsSubmodule mem_sUnitsSubmodule sUnitsRep val val_mem sUnits_eq_unit"
namespace Fg
p2m_open "NumberField.SUnits NumberField"

theorem finite_placesAbove (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) : (NumberField.SUnits.placesAbove E K S).Finite := by
  classical
  have hsub : NumberField.SUnits.placesAbove E K S ⊆
      ⋃ v ∈ S, (fun u : HeightOneSpectrum (𝓞 K) => u.asIdeal) ⁻¹' (v.asIdeal.primesOver (𝓞 K)) := by
    intro u hu
    rw [NumberField.SUnits.mem_placesAbove] at hu
    simp only [Set.mem_iUnion, Set.mem_preimage]
    exact ⟨u.under (𝓞 E), hu, u.isPrime, ⟨rfl⟩⟩
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun v _ => ?_) hsub
  haveI := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage fun x _ y _ h => HeightOneSpectrum.ext h

theorem moduleFinite_sUnitsSubmodule (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) : Module.Finite ℤ ↥(NumberField.SUnits.sUnitsSubmodule E K S) := by
  haveI : Finite ↥(NumberField.SUnits.placesAbove E K S) := (finite_placesAbove E K S).to_subtype
  obtain ⟨hfin, -⟩ := M4aHerbrand.finrank_sUnit_eq K (NumberField.SUnits.placesAbove E K S)
  have hmem : ∀ x : Kˣ, x ∈ NumberField.SUnits.sUnits E K S ↔ x ∈ (NumberField.SUnits.placesAbove E K S).unit K := by
    intro x
    rw [NumberField.SUnits.sUnits_eq_unit E K S]
  let e : Additive ↥((NumberField.SUnits.placesAbove E K S).unit K) ≃+ ↥(NumberField.SUnits.sUnitsSubmodule E K S) :=
    { toFun := fun a => ⟨Additive.ofMul ((Additive.toMul a : (NumberField.SUnits.placesAbove E K S).unit K) : Kˣ),
        (NumberField.SUnits.mem_sUnitsSubmodule E K S _).2 ((hmem _).2 (Additive.toMul a).2)⟩
      invFun := fun x => Additive.ofMul ⟨NumberField.SUnits.val E K S x, (hmem _).1 (NumberField.SUnits.val_mem E K S x)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact Module.Finite.equiv e.toIntLinearEquiv

end NumberField.SUnits.Fg

theorem solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) : Module.Finite ℤ (NumberField.SUnits.sUnitsRep E K S) := by
  convert NumberField.SUnits.Fg.moduleFinite_sUnitsSubmodule E K S using 1
  rfl
  rfl
  rfl

end S_NumberField_SUnits_moduleFinite_sUnitsRep
end P2MW
export P2MW.S_NumberField_SUnits_moduleFinite_sUnitsRep (solution)
