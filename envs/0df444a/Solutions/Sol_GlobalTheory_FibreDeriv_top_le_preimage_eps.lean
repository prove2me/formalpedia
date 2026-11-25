-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.top_le_preimage_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:08:08.050187+00:00
-- url     : https://prove2.me/submissions/d4d823dd-f0e7-4a3c-b5f3-bc30373bf928

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution (v : Sp (DualNumber ℂ) ⟶ X) (x : Sp ℂ ⟶ X)
    (hx : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  subst hx
  refine ⟨fun h p _ => h (Set.mem_univ _), fun h p _ => ?_⟩
  have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro q
    have : q ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
      intro b hb
      have hb' : b.fst = 0 := hb
      refine q.2.mem_of_pow_mem 2 ?_
      have : b ^ 2 = 0 := by
        ext <;> simp [pow_two, hb']
      rw [this]
      exact zero_mem _
    exact this
  obtain ⟨q, rfl⟩ := hs p
  exact h (Set.mem_univ q)
end GlobalTheory.FibreDeriv
