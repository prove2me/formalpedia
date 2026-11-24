-- Prove2me | solution 1 for GlobalTheory.KS.Sym.Der.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:28:25.20983+00:00
-- url     : https://prove2.me/submissions/75e47e40-d1db-4165-a1b9-eb42e1fce1ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
private lemma rsT_eq_resG_of_le_moduli {O₀ O : Z.Opens} (s : Γ(Z, O₀)) (h : O ≤ O₀) : rsT s O = resG Z h s := by
  unfold rsT
  rw [dif_pos h]
private lemma rsT_zero' {O₀ : Z.Opens} (O : Z.Opens) : rsT (0 : Γ(Z, O₀)) O = 0 := by
  unfold rsT
  split_ifs <;> simp
variable {K R : Type} [Field K] [CommRing R]
end GlobalTheory.KS.Sym
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
namespace GlobalTheory.KS.Sym
namespace Der
theorem _root_.solution {h : Z ⟶ X} {T : Z.Opens} {δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')}
    (a : Der h T δ) {W : X.Opens} (hW : IsAffineOpen W) (hT : T ≤ h ⁻¹ᵁ W) (h0 : ∀ f, δ W f T = 0)
    (O : X.Opens) (f : Γ(X, O)) (O' : Z.Opens) (h₁ : O' ≤ T) (h₂ : O' ≤ h ⁻¹ᵁ O) : δ O f O' = 0 := by
  have kill : ∀ (g : Γ(X, W)) (V : X.Opens), V ≤ W → ∀ O'' : Z.Opens, O'' ≤ T → O'' ≤ h ⁻¹ᵁ V →
      δ V (rsT g V) O'' = 0 := by
    intro g V hVW O'' k₁ k₂
    rw [a.2.1 W V g O'' hVW k₁ k₂, ← a.2.2 W g T O'' k₁ le_rfl hT, h0, rsT_zero']
  have loc : ∀ z : O', ∃ V : Z.Opens, V ≤ O' ∧ z.1 ∈ V ∧ rsT (δ O f O') V = 0 := by
    intro z
    have hz : h.base z.1 ∈ O ⊓ W := ⟨h₂ z.2, hT (h₁ z.2)⟩
    obtain ⟨b, hb, hzb⟩ := hW.exists_basicOpen_le (V := O ⊓ W) ⟨h.base z.1, hz⟩ hz.2
    refine ⟨h ⁻¹ᵁ X.basicOpen b ⊓ O', inf_le_right, ⟨hzb, z.2⟩, ?_⟩
    have hbO : X.basicOpen b ≤ O := hb.trans inf_le_left
    have hbW : X.basicOpen b ≤ W := hb.trans inf_le_right
    have k₁ : h ⁻¹ᵁ X.basicOpen b ⊓ O' ≤ T := inf_le_right.trans h₁
    have k₂ : h ⁻¹ᵁ X.basicOpen b ⊓ O' ≤ h ⁻¹ᵁ X.basicOpen b := inf_le_left
    have := hW.isLocalization_basicOpen b
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers b) (rsT f (X.basicOpen b))
    have hc' : rsT f (X.basicOpen b) * rsT (b ^ k) (X.basicOpen b) = rsT c (X.basicOpen b) := by
      rw [rsT_eq_resG_of_le_moduli (b ^ k) hbW, rsT_eq_resG_of_le_moduli c hbW]
      exact hc
    have e1 : δ (X.basicOpen b) (rsT f (X.basicOpen b) * rsT (b ^ k) (X.basicOpen b)) (h ⁻¹ᵁ X.basicOpen b ⊓ O') =
        δ (X.basicOpen b) (rsT c (X.basicOpen b)) (h ⁻¹ᵁ X.basicOpen b ⊓ O') := by
      rw [hc']
    rw [a.1 _ _ _ _ k₁ k₂, kill (b ^ k) _ hbW _ k₁ k₂, kill c _ hbW _ k₁ k₂, mul_zero, zero_add,
      a.2.1 O _ f _ hbO k₁ k₂, ← a.2.2 O f O' _ inf_le_right h₁ h₂] at e1
    have hu : IsUnit (pbT h (rsT (b ^ k) (X.basicOpen b)) (h ⁻¹ᵁ X.basicOpen b ⊓ O')) := by
      unfold pbT
      rw [dif_pos k₂]
      apply IsUnit.map
      rw [rsT_eq_resG_of_le_moduli _ hbW, map_pow]
      apply IsUnit.pow
      exact X.toRingedSpace.isUnit_res_basicOpen b
    exact hu.mul_right_eq_zero.mp e1
  choose V hVO hzV hV0 using loc
  refine TopCat.Sheaf.eq_of_locally_eq' Z.sheaf V O' (fun z => homOfLE (hVO z))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzV ⟨x, hx⟩⟩) _ 0 (fun z => ?_)
  have := hV0 z
  rw [rsT_eq_resG_of_le_moduli _ (hVO z)] at this
  change resG Z (hVO z) (δ O f O') = resG Z (hVO z) 0
  rw [map_zero]
  exact this
end Der
end GlobalTheory.KS.Sym
