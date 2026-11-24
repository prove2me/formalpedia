-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.exists_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:04.294832+00:00
-- url     : https://prove2.me/submissions/26cc9790-121e-49ba-ab20-daae3a88e2c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
import Theorems.Thm_GlobalTheory_TorsorUnit_comp_ev
import Theorems.Thm_GlobalTheory_TorsorUnit_cst_apply
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_univ
import Theorems.Thm_GlobalTheory_TorsorUnit_coaction_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
namespace GlobalTheory.TorsorUnit
theorem _root_.solution {α : A →+* C} (hα : α.FaithfullyFlat) {ρ : C →+* AddMonoidAlgebra C X}
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (χ : X) (p : Ideal A) (hp : p ≠ ⊤) :
    ∃ a ∉ p, ∃ c c' : C, c * c' = α a ∧ ρ c = AddMonoidAlgebra.single χ c := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  have hco := coaction_coeff (h _)
  obtain ⟨φ, hφ⟩ := (h (C ⊗[A] C)).2.2.2
    (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom
    Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := C) (B := C)).symm
  have h0 : ∀ c : C, ρ c = AddMonoidAlgebra.single 0 c → ∃ a, α a = c := by
    intro c hc
    have h1 := RingHom.congr_fun hφ c
    rw [RingHom.comp_apply, hc, ev_single] at h1
    refine (Algebra.IsEffective.of_faithfullyFlat A C c).1 ?_
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using h1
  have hρα : ∀ a, ρ (α a) = AddMonoidAlgebra.single 0 (α a) := by
    intro a
    have := RingHom.congr_fun ((h _).2.1 (cst X C) (univ X C)) a
    rwa [ev_univ] at this
  let ρ' : C →ₐ[A] AddMonoidAlgebra C X := { ρ with commutes' := hρα }
  let κ : C →ₐ[A] AddMonoidAlgebra C X := { cst X C with commutes' := fun _ => rfl }
  let Φ : C ⊗[A] C →ₐ[A] AddMonoidAlgebra C X :=
    Algebra.TensorProduct.lift ρ' κ fun _ _ => Commute.all _ _
  have hΦ : ∀ c c' : C, Φ (c ⊗ₜ c') = ρ c * AddMonoidAlgebra.single 0 c' := fun _ _ => rfl
  have hu : (Units.map Φ.toRingHom.toMonoidHom).comp φ = univ X C := by
    apply (h _).2.2.1 (cst X C)
    have h1 := congrArg (Φ.toRingHom.comp ·) hφ
    simp only [← RingHom.comp_assoc, comp_ev] at h1
    have h2 : Φ.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom = cst X C := by
      refine RingHom.ext fun c => ?_
      change Φ (1 ⊗ₜ c) = _
      rw [hΦ, map_one, _root_.one_mul, cst_apply]
    rw [h2] at h1
    rw [← h1, ev_univ]
    refine RingHom.ext fun c => ?_
    change Φ (c ⊗ₜ 1) = ρ c
    rw [hΦ, ← AddMonoidAlgebra.one_def, _root_.mul_one]
  have hχ : Φ (φ (Multiplicative.ofAdd χ)).val = AddMonoidAlgebra.single χ 1 :=
    congrArg Units.val (DFunLike.congr_fun hu (Multiplicative.ofAdd χ))
  by_contra! hcon
  have key : ∀ e : C ⊗[A] C, ∃ a ∈ p, α a = (ρ ((Φ e).coeff χ)).coeff 0 := by
    intro e
    induction e using TensorProduct.induction_on with
    | zero => exact ⟨0, p.zero_mem, by simp⟩
    | add e e' he he' =>
      obtain ⟨a, ha, h1⟩ := he
      obtain ⟨a', ha', h1'⟩ := he'
      exact ⟨a + a', p.add_mem ha ha', by simp [h1, h1']⟩
    | tmul c c' =>
      have h1 : (Φ (c ⊗ₜ c')).coeff χ = (ρ c).coeff χ * c' := by
        rw [hΦ]; simp
      have h2 : (ρ ((ρ c).coeff χ * c')).coeff 0 = (ρ c).coeff χ * (ρ c').coeff (-χ) := by
        rw [map_mul, hco]; simp
      obtain ⟨a, ha⟩ := h0 ((ρ c).coeff χ * (ρ c').coeff (-χ)) (by
        rw [map_mul, hco, hco, AddMonoidAlgebra.single_mul_single, add_neg_cancel])
      refine ⟨a, ?_, by rw [h1, h2, ha]⟩
      by_contra hap
      exact hcon a hap _ _ ha.symm (hco c χ)
  obtain ⟨a, ha, h1⟩ := key (φ (Multiplicative.ofAdd χ)).val
  rw [hχ] at h1
  have h2 : α a = α 1 := by simpa [AddMonoidAlgebra.one_def] using h1
  exact hp ((Ideal.eq_top_iff_one p).2 (hα.injective h2 ▸ ha))
end GlobalTheory.TorsorUnit
