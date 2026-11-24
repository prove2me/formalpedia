-- Prove2me | solution 1 for GlobalTheory.KS.TangentAt.existsUnique_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:22:53.213802+00:00
-- url     : https://prove2.me/submissions/e461cbd5-dc05-45e1-b632-0763f9878592

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
import Theorems.Thm_GlobalTheory_KS_TangentAt_top_le_iff_dual
import Theorems.Thm_GlobalTheory_KS_TangentAt_comp_eq_spMap
import Theorems.Thm_GlobalTheory_KS_TangentAt_ex_zero
import Theorems.Thm_GlobalTheory_KS_TangentAt_diffAt_iff
import Theorems.Thm_GlobalTheory_KS_PtDual_existsUnique_point

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
namespace GlobalTheory.KS.TangentAt
private theorem top_le_preimage_top' {X Y : Scheme.{0}} (f : X ⟶ Y) : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
end GlobalTheory.KS.TangentAt
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.TangentAt
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
namespace GlobalTheory.KS.TangentAt
theorem _root_.solution (htan : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (z : Fin g → ℂ)
    (δ : ∀ W : A.left.Opens, Γ(A.left, W) → ℂ) (hδ : PtDer (u.ex z).left δ)
    (hc : ∀ a, δ ⊤ (constFn A.hom ⊤ a) = 0) :
    ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by
  obtain ⟨v, ⟨hv0, hvd⟩, -⟩ := PtDual.existsUnique_point hδ
  have hv0' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (u.ex z).left := hv0
  have hvd' : ∀ (W : A.left.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(A.left, W)), (dval v W h f).snd = δ W f := hvd
  have hone : (u.ex 0).left = (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [ex_zero]
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ (tr u (-z)).left =
      (η : 𝟙_ (Over (Sp ℂ)) ⟶ A).left := by
    rw [← Category.assoc, hv0', ← Over.comp_left, ex_tr, neg_add_cancel, hone]
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v ≫ (tr u (-z)).left) ≫ A.hom = 𝟙 _ := by
    rw [← Category.assoc, h0]
    exact Over.w _
  have hc' : ∀ a, (dval (v ≫ (tr u (-z)).left) ⊤ (top_le_preimage_top' _) (constFn A.hom ⊤ a)).snd = 0 := by
    intro a
    rw [dval_comp v (tr u (-z)).left ⊤ _ ⊤ (top_le_preimage_top' _) (top_le_preimage_top' _), hvd']
    have e3 := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE (tr u (-z)).left A.hom ⊤ ⊤ ⊤ (top_le_preimage_top' _)
        (top_le_preimage_top' _))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
    have key : ∀ (k : A.left ⟶ Sp ℂ) (_ : k = A.hom) (e : ⊤ ≤ k ⁻¹ᵁ ⊤),
        (k.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = constFn A.hom ⊤ a := by
      rintro _ rfl e
      rfl
    have e4 : ((tr u (-z)).left.appLE ⊤ ⊤ (top_le_preimage_top' _)).hom (constFn A.hom ⊤ a) =
        constFn A.hom ⊤ a := e3.trans (key _ (Over.w _) _)
    rw [e4]
    exact hc a
  let v'' : epsR ℂ ⟶ A := Over.homMk (v ≫ (tr u (-z)).left) (comp_eq_spMap A.hom _ h1 hc')
  have htv : IsTangent v'' := h0
  obtain ⟨w, hw, huniq⟩ := htan v'' htv
  have hdiff : ∀ w', u.IsDiff w' v'' ↔ DiffAt u (v ≫ (tr u (-z)).left) 0 w' := fun _ => Iff.rfl
  refine ⟨w, ?_, ?_⟩
  · intro O f hO
    have hv : ⊤ ≤ v ⁻¹ᵁ O := (top_le_iff_dual v O).2 (by rw [hv0']; exact hO)
    rw [← hvd' O hv f]
    exact ((diffAt_iff u v z w).2 ((hdiff w).1 hw)) O hv f
  · intro w' hw'
    apply huniq
    rw [hdiff, ← diffAt_iff]
    intro U h f
    rw [hvd' U h f]
    exact hw' U f (by rw [← hv0']; exact (top_le_iff_dual v U).1 h)
end GlobalTheory.KS.TangentAt
