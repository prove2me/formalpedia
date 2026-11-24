-- Prove2me | solution 1 for GlobalTheory.TangentCrit.formallySmooth_of_dual_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:20.854918+00:00
-- url     : https://prove2.me/submissions/1fad1924-79bc-4199-917e-a875516d8d31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_TangentCrit_formallySmooth_of_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B]
namespace GlobalTheory.TangentCrit
theorem _root_.solution [Field k] [IsLocalRing B] (α : R →+* A) (β : A →+* B)
    (hA : α.EssFiniteType) (hB : (β.comp α).EssFiniteType) (hs : (β.comp α).FormallySmooth)
    (x : B →+* k) [IsLocalHom x]
    (H : ∀ ψ : A →+* DualNumber k, (∀ a, (ψ a).fst = x (β a)) → (∀ r, (ψ (α r)).snd = 0) →
      ∃ φ : B →+* DualNumber k, (∀ b, (φ b).fst = x b) ∧ ∀ a, φ (β a) = ψ a) :
    β.FormallySmooth := by
  algebraize [α, β, β.comp α, x, x.comp β, (x.comp β).comp α]
  have : IsScalarTower R B k := .of_algebraMap_eq' rfl
  haveI : IsLocalHom (algebraMap B k) := ‹_›
  letI : Algebra (IsLocalRing.ResidueField B) k := (IsLocalRing.ResidueField.lift x).toAlgebra
  haveI : IsScalarTower B (IsLocalRing.ResidueField B) k := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Free B Ω[B⁄R] := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (KaehlerDifferential.mapBaseChange R A B)).mpr (lTensor_injective_of_extend (k := k) _ fun χ => by
      let D : Derivation R A k :=
        ((χ.restrictScalars A) ∘ₗ TensorProduct.mk A B Ω[A⁄R] 1).compDer (KaehlerDifferential.D R A)
      obtain ⟨φ, h₁, h₂⟩ := H (derToDual D) (fun a => fst_derToDual D a)
        (fun r => (snd_derToDual D _).trans (D.map_algebraMap r))
      let E : Derivation R B k := dualToDer φ h₁ (fun r => by
        change (φ (β (α r))).snd = 0
        rw [h₂]; exact (snd_derToDual D _).trans (D.map_algebraMap r))
      refine ⟨E.liftKaehlerDifferential, ?_⟩
      refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring ?_)
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
      have : E (algebraMap A B a) = D a := by
        change (φ (β a)).snd = _
        rw [h₂, snd_derToDual]
      simpa [D, KaehlerDifferential.map_D] using this)
  exact formallySmooth_of_split r hr
end GlobalTheory.TangentCrit
