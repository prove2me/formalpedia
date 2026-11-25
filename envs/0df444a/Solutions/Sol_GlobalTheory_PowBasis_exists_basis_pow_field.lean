-- Prove2me | solution 1 for GlobalTheory.PowBasis.exists_basis_pow_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:22.959929+00:00
-- url     : https://prove2.me/submissions/23c6cb92-dae5-4387-8a79-3ea9e10a7514

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
import Theorems.Thm_GlobalTheory_PowBasis_exists_basis_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowBasis
namespace GlobalTheory.PowBasis
theorem _root_.solution : SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∀ t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)), ∃! c : Fin (k ^ A.g) → F, ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j := by
  intro hT R _ _ A F _ _ k hk
  obtain ⟨b, hb⟩ := exists_basis_pow hT A k hk F (jFK (R := R) F)
  refine ⟨b, fun t => ?_⟩
  obtain ⟨r, hr, hu⟩ := hb t
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (r i), fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun x => liftFun A.A _ x * (b i).f j)
      ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply (r i)).symm
  · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) hc
    funext i
    rw [← congrFun e i]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply (c i)).symm
end GlobalTheory.PowBasis
