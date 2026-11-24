-- Prove2me | solution 1 for GlobalTheory.KS.Sym.Der.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:31:04.562297+00:00
-- url     : https://prove2.me/submissions/1939ffd3-404d-4b56-a871-d156a7ad0b90

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
private lemma rsT_sub_moduli {O₀ : Z.Opens} (a b : Γ(Z, O₀)) (O : Z.Opens) :
    rsT (a - b) O = rsT a O - rsT b O := by
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
theorem _root_.solution {h : Z ⟶ X} {T : Z.Opens} {δ δ' : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')}
    (a : Der h T δ) (b : Der h T δ') : Der h T (fun O f O' => δ O f O' - δ' O f O') := by
  unfold Der at a b ⊢
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  refine ⟨fun O f f' O' h₁ h₂ => ?_, fun O O₁ f O' h₀ h₁ h₂ => ?_, fun O f O' O'' h₀ h₁ h₂ => ?_⟩
  · dsimp only
    rw [a1 O f f' O' h₁ h₂, b1 O f f' O' h₁ h₂]
    ring
  · dsimp only
    rw [a2 O O₁ f O' h₀ h₁ h₂, b2 O O₁ f O' h₀ h₁ h₂]
  · dsimp only
    rw [rsT_sub_moduli, a3 O f O' O'' h₀ h₁ h₂, b3 O f O' O'' h₀ h₁ h₂]
end Der
end GlobalTheory.KS.Sym
