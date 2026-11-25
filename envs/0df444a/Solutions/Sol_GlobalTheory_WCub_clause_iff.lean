-- Prove2me | solution 1 for GlobalTheory.WCub.clause_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:07:54.918126+00:00
-- url     : https://prove2.me/submissions/cd29a824-4c47-4e3c-b713-26c6284e2c31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.WCub
theorem _root_.solution {T XB XG E : Scheme.{0}} {K : Type} [Fintype K] (mB : T ⟶ XB) (mG : T ⟶ XG) (p : K → (T ⟶ E))
    (UB : XB.Opens) (UG : XG.Opens) (W : K → E.Opens) (a : Γ(XB, UB)ˣ) (b : Γ(XG, UG)ˣ) (c : ∀ k, Γ(E, W k)ˣ)
    (ε : K → ℤ) :
    (∀ (V : T.Opens) (hB : V ≤ mB ⁻¹ᵁ UB) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k),
      res hB (pullU mB UB a) = (∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) ↔
    ∀ y : T, mB y ∈ UB → mG y ∈ UG → (∀ k, p k y ∈ W k) →
      gm mB y UB a = (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := by
  have one : ∀ {X : Scheme.{0}} (m : T ⟶ X) (U : X.Opens) (V : T.Opens) (h : V ≤ m ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (y : T),
      y ∈ V → gm (𝟙 T) y V (res h (pullU m U u)) = gm m y U u := fun m U V h u y hy =>
    (gm_res (𝟙 T) y h hy _).trans ((gm_pull (𝟙 T) m y U (h hy) u).trans (by rw [Category.id_comp]))
  have key : ∀ (V : T.Opens) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k) (y : T), y ∈ V →
      gm (𝟙 T) y V ((∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) =
        (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := fun V hG hw y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
      (map_zpow _ _ _).trans (congrArg (· ^ ε k) (one _ _ V _ _ y hy)))) (one _ _ V _ _ y hy))
  constructor
  · intro H y hB hG hw
    let V : T.Opens := mB ⁻¹ᵁ UB ⊓ mG ⁻¹ᵁ UG ⊓ ⟨⋂ k, (p k ⁻¹ᵁ W k : Set T), isOpen_iInter_of_finite fun k =>
      (p k ⁻¹ᵁ W k).isOpen⟩
    have hy : y ∈ V := ⟨⟨hB, hG⟩, Set.mem_iInter.2 hw⟩
    have l : ∀ k, V ≤ p k ⁻¹ᵁ W k := fun k z hz => Set.mem_iInter.1 hz.2 k
    have e := congrArg (gm (𝟙 T) y V) (H V (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) l)
    exact (one _ _ V _ _ y hy).symm.trans (e.trans (key V _ _ y hy))
  · intro H V hB hG hw
    exact unit_ext fun y hy => (one _ _ V _ _ y hy).trans ((H y (hB hy) (hG hy) fun k => hw k hy).trans
      (key V _ _ y hy).symm)
end GlobalTheory.WCub
