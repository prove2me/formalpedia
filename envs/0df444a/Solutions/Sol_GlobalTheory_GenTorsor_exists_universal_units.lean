-- Prove2me | solution 1 for GlobalTheory.GenTorsor.exists_universal_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:43.412416+00:00
-- url     : https://prove2.me/submissions/4763be0e-98dd-493d-9c98-1c75d3ac4f3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.GenTorsor
theorem _root_.solution (K : Type) :
    ∃ (T : Scheme.{0}) (e : K → Γ(T, ⊤)ˣ), ∀ (Z : Scheme.{0}) (u : K → Γ(Z, ⊤)ˣ),
      ∃! c : Z ⟶ T, ∀ k, pb c ⊤ ⊤ le_rfl (e k) = u k := by
  let A := MonoidAlgebra ℤ (Multiplicative (FreeAbelianGroup K))
  let ε : K → Aˣ := fun k =>
    (MonoidAlgebra.of ℤ (Multiplicative (FreeAbelianGroup K))).toHomUnits
      (Multiplicative.ofAdd (FreeAbelianGroup.of k))
  have hext : ∀ (R : Type) [CommRing R] (φ ψ : A →+* R), (∀ k, φ (ε k) = ψ (ε k)) → φ = ψ := by
    intro R _ φ ψ h
    have : (φ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits =
        (ψ.toMonoidHom.comp (MonoidAlgebra.of ℤ _)).toHomUnits := by
      apply MonoidHom.toAdditiveRight.injective
      apply FreeAbelianGroup.lift.symm.injective
      funext k
      exact congrArg Additive.ofMul (Units.ext (h k))
    apply MonoidAlgebra.ringHom_ext
    · intro b; exact (eq_intCast (φ.comp MonoidAlgebra.singleOneRingHom) b).trans
        (eq_intCast (ψ.comp MonoidAlgebra.singleOneRingHom) b).symm
    · intro g
      exact congrArg (fun f => (f g : R)) this
  have hex : ∀ (R : Type) [CommRing R] (u : K → Rˣ), ∃ φ : A →+* R, ∀ k, φ (ε k) = u k := by
    intro R _ u
    refine ⟨(MonoidAlgebra.lift ℤ R _ ((Units.coeHom R).comp (MonoidHom.toAdditiveRight.symm
      (FreeAbelianGroup.lift fun k => Additive.ofMul (u k))))).toRingHom, fun k => ?_⟩
    simp [ε, A]
  let i := Scheme.ΓSpecIso (CommRingCat.of A)
  refine ⟨Spec (.of A), fun k => Units.map i.inv.hom (ε k), fun Z u => ?_⟩
  have hpb : ∀ (c : Z ⟶ Spec (.of A)) k,
      (pb c ⊤ ⊤ le_rfl (Units.map i.inv.hom (ε k))).val = (i.inv ≫ c.appTop).hom (ε k) := by
    intro c k
    have e : c.appLE ⊤ ⊤ le_rfl = c.appTop := (c.app_eq_appLE (U := ⊤)).symm
    change (c.appLE ⊤ ⊤ le_rfl).hom _ = _
    rw [e]; rfl
  obtain ⟨φ, hφ⟩ := hex _ u
  refine existsUnique_of_exists_of_unique ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), fun k => ?_⟩ ?_
  · apply Units.ext
    rw [hpb, ← hφ]
    have : i.inv ≫ (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
      simp [i, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [this]; rfl
  · intro c c' h h'
    apply ext_of_isAffine
    rw [← cancel_epi i.inv]
    ext1
    apply hext
    intro k
    rw [← hpb, ← hpb, h, h']
end GlobalTheory.GenTorsor
