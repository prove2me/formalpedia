-- Prove2me | solution 1 for GlobalTheory.PowBasis.exists_basis_of_formEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:52.306816+00:00
-- url     : https://prove2.me/submissions/eccdc933-793a-473a-949e-8b0843f8e06c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsBasisOfFormEq
import Theorems.Thm_GlobalTheory_PowBasis_comb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec


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
theorem _root_.solution {S : Scheme.{0}} {A T : Over S} {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ X)} {ε : K → ℤ}
    {φ' : K' → ((T ⊗ A).left ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') {m : ℕ}
    {b : Fin m → LB.Sec (LB.LinComb L φ ε)} (hb : IsSecBasis _ b) :
    ∃ b' : Fin m → LB.Sec (LB.LinComb L φ' ε'), IsSecBasis _ b' := by
  choose b' hb' using fun i => exists_sec hL h (b i)
  refine ⟨b', fun t => ?_⟩
  obtain ⟨s, hs⟩ := exists_sec hL (φ := φ') (ε := ε') (φ' := φ) (ε' := ε) (fun U _ g => (h U g).symm) t
  refine (existsUnique_congr fun r => ?_).1 (hb s)
  refine (comb_iff hL s b fun i => (fst T A).left.appTop.hom (r i)).trans
    (Iff.trans ?_ (comb_iff hL t b' fun i => (fst T A).left.appTop.hom (r i)).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [hs _ _ y J hJ]
  simp only [hb' _ _ _ y J hJ]
end GlobalTheory.PowBasis
