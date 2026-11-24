-- Prove2me | solution 1 for GlobalTheory.CechDR.hasLoc_OAff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:18:25.245042+00:00
-- url     : https://prove2.me/submissions/2b65e9f7-4578-46f8-9a8c-c9e1854733de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasLocOAff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R'),
    Desc.HasLoc (OAff s') := by
  intro R' _ X' s' T b
  let U := T.unop
  let b' : Γ(X', U.1) := b
  let V : X'.affineOpens := ⟨X'.basicOpen b', U.2.basicOpen b'⟩
  have hVU : V ≤ U := X'.basicOpen_le b'
  let l : T ⟶ Opposite.op V := (homOfLE hVU).op
  haveI := U.2.isLocalization_basicOpen b'
  refine ⟨Opposite.op V, l, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit (S := Γ(X', X'.basicOpen b')) b'
  · intro y
    let y' : Γ(X', X'.basicOpen b') := y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers b') y'
    refine ⟨n, x, ?_⟩
    show y' * (algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') b') ^ n =
      algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x
    rw [← map_pow]
    exact e
  · intro x hx
    let x' : Γ(X', U.1) := x
    have hx : algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x' = 0 := hx
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b') _ x').1 hx
    exact ⟨n, e⟩
  · intro S u hu
    have hSU : S.unop.1 ≤ U.1 := leOfHom u.unop
    have hu' : IsUnit ((X'.presheaf.map (homOfLE hSU).op).hom b') := hu
    have h1 := X'.basicOpen_res b' (homOfLE hSU).op
    rw [Scheme.basicOpen_of_isUnit _ hu'] at h1
    have hSV : S.unop ≤ V := by
      change S.unop.1 ≤ X'.basicOpen b'
      rw [h1]; exact inf_le_right
    refine ⟨(homOfLE hSV).op, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩
end GlobalTheory.CechDR
