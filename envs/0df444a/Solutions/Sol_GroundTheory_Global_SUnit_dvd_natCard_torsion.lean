-- Prove2me | solution 1 for GroundTheory.Global.SUnit.dvd_natCard_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:04.585736+00:00
-- url     : https://prove2.me/submissions/f7978a3b-641e-4872-a49b-d8e8de34aaed

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.Global.SUnit
namespace GroundTheory.Global.SUnit
theorem _root_.solution (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion (S.unit K)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  set u : Kˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hfin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, ← hu.eq_orderOf]
    exact NeZero.pos n
  let u' : S.unit K := ⟨u, fun v _ ↦ valuation_eq_one_of_isOfFinOrder hfin v⟩
  have hfin' : IsOfFinOrder u' := by
    rw [← orderOf_pos_iff, ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact orderOf_pos_iff.mpr hfin
  let t : CommGroup.torsion (S.unit K) := ⟨u', hfin'⟩
  have ht : orderOf t = n := by
    rw [← orderOf_injective (CommGroup.torsion (S.unit K)).subtype Subtype.val_injective,
      ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact hu.eq_orderOf.symm
  rw [← ht]
  exact orderOf_dvd_natCard t
end GroundTheory.Global.SUnit
