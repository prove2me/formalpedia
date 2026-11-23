-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.exists_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.213227+00:00
-- url     : https://prove2.me/submissions/dbab36ff-23e5-49de-be83-bba8b0aaf2ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (C : Type) [Field C] [IsAlgClosed C] (k : ℕ) (hk : (k : C) ≠ 0) :
    ∃ ζ : Cˣ, IsPrimitiveRoot ζ k ∧ ∃ e : Multiplicative (ZMod k) →* Cˣ, Function.Injective e ∧
      ∀ u : Cˣ, u ^ k = 1 → ∃ z, e z = u := by
  haveI : NeZero (k : C) := ⟨hk⟩
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C k
  have h := hz.isUnit_unit (NeZero.ne k)
  refine ⟨_, h, (Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).toMonoidHom, ?_, ?_⟩
  · exact Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).injective
  · intro u hu
    have : u ∈ Subgroup.zpowers _ := h.zpowers_eq ▸ (mem_rootsOfUnity k u).2 hu
    obtain ⟨y, hy⟩ := (AddEquiv.toMultiplicativeLeft h.zmodEquivZPowers).surjective ⟨u, this⟩
    exact ⟨y, congrArg Subtype.val hy⟩
end GlobalTheory.Ex.QStr
