-- Prove2me | solution 1 for GlobalTheory.length_localizedModule_quotient_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:49.405471+00:00
-- url     : https://prove2.me/submissions/21d50682-b26c-4425-8611-893aac534d78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution (m : Ideal S) [hm : m.IsMaximal] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl (S ⧸ m)) = 1 := by
  haveI : IsSimpleModule S (S ⧸ m) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl _ _⟩⟩
  haveI : IsLocalizedModule m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m) :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        refine LinearMap.bijective_of_ne_zero fun h => s.2 ?_
        have := LinearMap.congr_fun h (Ideal.Quotient.mk m 1)
        simp only [Module.algebraMap_end_apply, LinearMap.zero_apply] at this
        rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero] at this
        simpa using this
      surj := fun y => ⟨(y, 1), by simp⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  let e := IsLocalizedModule.iso m.primeCompl (LinearMap.id : S ⧸ m →ₗ[S] S ⧸ m)
  haveI : Nontrivial (LocalizedModule m.primeCompl (S ⧸ m)) := e.toEquiv.nontrivial
  apply le_antisymm
  · rw [← Module.length_top]
    refine (Submodule.length_le_length_restrictScalars S _).trans ?_
    rw [Submodule.restrictScalars_top, Module.length_top, e.length_eq, Module.length_eq_one]
  · exact Order.one_le_iff_pos.mpr Module.length_pos
end GlobalTheory
