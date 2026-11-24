-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_descent_of_isGaloisCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:07:15.213105+00:00
-- url     : https://prove2.me/submissions/779c01be-dc8e-407a-989b-ec86a600c9be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentLinearisedLineBundleGaloisCover
import Theorems.Thm_GlobalTheory_LinDescent_locTransitive_of_isGaloisCover
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_etale
import Theorems.Thm_GlobalTheory_LinDescent_exists_descent_of_galois


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.LinDescent
namespace GlobalTheory.LinDescent
theorem _root_.solution :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  intro X Y π Ga _ ρ L hG hL u hu hc
  have : Finite Ga := hG.finite
  have : IsFinite π := hG.fin
  have : Etale π := hG.etale
  have : Surjective π := hG.onto
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ ρ c := by
    intro k _ _ r a b hab
    obtain ⟨d, -, hd⟩ := hG.fibre k r (r ≫ ρ a) (by rw [Category.assoc, hG.inv])
    exact (hd a rfl).trans (hd b hab.symm).symm
  exact exists_descent_of_galois hL hG.one (fun a c => (hG.mul a c).symm) hG.inv
    (locTransitive_of_isGaloisCover hG) hfree hu hc
end GlobalTheory.LinDescent
