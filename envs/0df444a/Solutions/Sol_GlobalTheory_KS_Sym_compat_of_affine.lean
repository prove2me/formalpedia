-- Prove2me | solution 1 for GlobalTheory.KS.Sym.compat_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:55:27.778749+00:00
-- url     : https://prove2.me/submissions/bddba992-f664-41f7-a0a5-7c141b025412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
import Theorems.Thm_GlobalTheory_KS_Sym_pbT_id
import Theorems.Thm_GlobalTheory_KS_Sym_Der_sub
import Theorems.Thm_GlobalTheory_KS_Sym_Der_eq_zero
import Theorems.Thm_GlobalTheory_KS_Sym_tr_eq
import Theorems.Thm_GlobalTheory_KS_Sym_der_tr
import Theorems.Thm_GlobalTheory_KS_IsCob_sub

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
private lemma rsT_self' {O₀ : Z.Opens} (s : Γ(Z, O₀)) : rsT s O₀ = s := by
  unfold rsT
  rw [dif_pos le_rfl]
  show (Z.presheaf.map (𝟙 (Opposite.op O₀))).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl
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
variable {K R : Type} [Field K] [CommRing R]
namespace GlobalTheory.KS.Sym
theorem _root_.solution {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K} {W : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (hW : IsAffineOpen W)
    {q₂ : Z ⟶ Sp K} {s₂ : X₂ ⟶ Sp R} {m₂ : Z ⟶ X₂} {Q : X₂.Opens}
    {d₂ : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Z, m₂ ⁻¹ᵁ O)} (hd₂ : LocDerK q₂ s₂ m₂ D Q d₂) {π : X₂ ⟶ X} {p : Z ⟶ Y}
    (sq : m₂ ≫ π = p ≫ m) (hQ : Q ≤ π ⁻¹ᵁ W) (h0 : ∀ f : Γ(X, W), d₂ Q (pbT π f Q) = pbT p (d W f) _)
    {O : X.Opens} (hO : O ≤ W) (f : Γ(X, O)) {O₂ : X₂.Opens} (h₁ : O₂ ≤ Q) (h₂ : O₂ ≤ π ⁻¹ᵁ O) :
    d₂ O₂ (pbT π f O₂) = pbT p (d O f) _ := by
  have key : ∀ x, π.base (m₂.base x) = m.base (p.base x) := fun x => by
    simpa using congrArg (fun φ : Z ⟶ X => φ.base x) sq
  have hTW : m₂ ⁻¹ᵁ Q ≤ p ⁻¹ᵁ m ⁻¹ᵁ W := fun x hx => by
    have b1 : π.base (m₂.base x) ∈ W := hQ hx
    rw [key] at b1
    exact b1
  have hp : m₂ ⁻¹ᵁ O₂ ≤ p ⁻¹ᵁ m ⁻¹ᵁ O := fun x hx => by
    have b1 : π.base (m₂.base x) ∈ O := h₂ hx
    rw [key] at b1
    exact b1
  have D₂ := der_tr hd₂ (𝟙 Z) π (h := m₂ ≫ π) (Category.id_comp _).symm (T := m₂ ⁻¹ᵁ Q) (fun x hx => hx)
  have D₁ := der_tr hd p (𝟙 X) (h := m₂ ≫ π) (by rw [Category.comp_id, sq]) (T := m₂ ⁻¹ᵁ Q) hTW
  have h0' : ∀ g : Γ(X, W),
      tr (𝟙 Z) m₂ π Q d₂ W g (m₂ ⁻¹ᵁ Q) - tr p m (𝟙 X) W d W g (m₂ ⁻¹ᵁ Q) = 0 := by
    intro g
    rw [tr_eq hd₂ (𝟙 Z) π g (O₃ := Q) (O' := m₂ ⁻¹ᵁ Q) hQ le_rfl (fun x hx => hx),
      tr_eq hd p (𝟙 X) g (O₃ := W) (fun x hx => hx) le_rfl hTW,
      pbT_id, pbT_id, rsT_self', rsT_self', h0, sub_self]
  have E := Der.eq_zero (Der.sub D₂ D₁) hW (fun x hx => hQ hx) h0' O f (m₂ ⁻¹ᵁ O₂)
    (fun x hx => h₁ hx) (fun x hx => h₂ hx)
  beta_reduce at E
  rw [tr_eq hd₂ (𝟙 Z) π f (O₃ := O₂) (O' := m₂ ⁻¹ᵁ O₂) h₂ h₁ (fun x hx => hx),
    tr_eq hd p (𝟙 X) f (O₃ := O) (fun x hx => hx) hO hp,
    pbT_id, pbT_id, rsT_self', rsT_self', sub_eq_zero] at E
  exact E
end GlobalTheory.KS.Sym
