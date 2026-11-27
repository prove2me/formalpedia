-- Prove2me | solution 1 for GroundTheory.Global.Artin.exists_frobElem_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:40.624397+00:00
-- url     : https://prove2.me/submissions/f5a13c67-c67c-482d-ba88-4f388dcf3420

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_frobElem_of_isArithFrobAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
namespace GroundTheory.Global.Artin
theorem _root_.solution {φ : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (x : Gal(L/K)) :
    ∃ φx : H, (∃ i ∈ (MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)),
        (φx : Gal(L/K)) = x * φ ^ (frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.asIdeal.inertia Gal(L/K)) x : ℤ) * x⁻¹ * i) ∧
      IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal) := by
  have : (x • w.asIdeal).IsMaximal := (x • w).isMaximal
  obtain ⟨φx, hφx⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 (fixedField H)) H (x • w.asIdeal)
  exact ⟨φx, frobElem_of_isArithFrobAt H w hφ x φx hφx, hφx⟩
end GroundTheory.Global.Artin
