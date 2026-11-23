-- Prove2me | solution 1 for GlobalTheory.LocDerExt.der_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:09.784385+00:00
-- url     : https://prove2.me/submissions/552fa3b6-c577-4e4b-8fd8-4948fb944dff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExt
namespace GlobalTheory.LocDerExt
theorem _root_.solution {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (d : A → C)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = φ (algebraMap A B a) * d b + φ (algebraMap A B b) * d a) :
    ∃ δ : B → C, (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = φ a * δ b + φ b * δ a) ∧
      ∀ a, δ (algebraMap A B a) = d a := by
  have h0 : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h1 : d 1 = 0 := by
    have := hmul 1 1
    simp only [_root_.mul_one, map_one, _root_.one_mul] at this
    exact left_eq_add.mp this
  obtain ⟨ψ, hψ1, hψ2⟩ : ∃ ψ : A →+* DualNumber C, (∀ a, (ψ a).fst = φ (algebraMap A B a)) ∧
      ∀ a, (ψ a).snd = d a :=
    ⟨{ toFun := fun a => TrivSqZeroExt.inl (φ (algebraMap A B a)) + TrivSqZeroExt.inr (d a)
       map_one' := by ext <;> simp [h1]
       map_zero' := by ext <;> simp [h0]
       map_add' := fun a b => by ext <;> simp [hadd]
       map_mul' := fun a b => by ext <;> simp [hmul, mul_comm] }, fun a => by simp, fun a => by simp⟩
  have hu : IsUnit (ψ f) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ1]
    exact (IsLocalization.Away.algebraMap_isUnit f).map φ
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : B →+* DualNumber C, ∀ a, Ψ (algebraMap A B a) = ψ a :=
    ⟨IsLocalization.Away.lift f hu, fun a => IsLocalization.Away.lift_eq f hu a⟩
  obtain ⟨π, hπ⟩ : ∃ π : DualNumber C →+* C, ∀ x, π x = x.fst :=
    ⟨(TrivSqZeroExt.fstHom C C C).toRingHom, fun _ => rfl⟩
  have hf : π.comp Ψ = φ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply, hΨ, hπ, hψ1]
  have hf' : ∀ b, (Ψ b).fst = φ b := fun b => by rw [← hf, RingHom.comp_apply, hπ]
  refine ⟨fun b => (Ψ b).snd, fun a b => by simp only [map_add, TrivSqZeroExt.snd_add],
    fun a b => ?_, fun a => by simp only [hΨ, hψ2]⟩
  simp only [map_mul, DualNumber.snd_mul, hf']
  ring
end GlobalTheory.LocDerExt
