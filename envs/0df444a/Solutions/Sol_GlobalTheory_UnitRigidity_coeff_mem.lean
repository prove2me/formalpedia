-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:48.562169+00:00
-- url     : https://prove2.me/submissions/df38dcb9-1fe6-49ec-9cb9-15b8f90dc135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_UnitRigidity_exists_normalised
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {K L B ι : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (b : Module.Basis ι K B) (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L]
    [NoZeroDivisors (IsLocalRing.ResidueField O ⊗[K] B)] (ψ : B →ₐ[K] K)
    (u : L ⊗[K] B) (hu : IsUnit u)
    (h1 : Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) u = 1) (i : ι) :
    (Algebra.TensorProduct.basis L b).repr u i ∈ O := by
  have : Nontrivial B := ψ.toRingHom.domain_nontrivial
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨a, u', ha, eu, hu', hcu⟩ := exists_normalised b O u hu.ne_zero
  obtain ⟨c, w', hc, ew, hw', -⟩ := exists_normalised b O w (right_ne_zero_of_mul_eq_one hw)
  set j := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O L) (AlgHom.id K B) with hj
  set r := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
    (AlgHom.id K B) with hr
  set e := Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) with he
  set e' := Algebra.TensorProduct.lift (AlgHom.id K O) ((Algebra.ofId K O).comp ψ)
      (fun _ _ => Commute.all _ _) with he'
  have hjinj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B)
      (IsScalarTower.toAlgHom K O L).toLinearMap Subtype.val_injective
  have hej : ∀ z, e (j z) = (e' z : L) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y =>
      simp [he, he', hj, Algebra.ofId_apply]
      left
      exact IsScalarTower.algebraMap_apply K O L _
    | add x y hx hy => simp [hx, hy]
  have hes : ∀ (x : L) z, e (x • z) = x * e z := by
    intro x z
    rw [Algebra.smul_def, map_mul]
    simp [he]
  have hprod : (a * c) • j (u' * w') = 1 := by
    rw [← hw, eu, ew, map_mul, smul_mul_smul_comm]
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  have hunit : IsUnit (e' u') := by
    refine isUnit_of_mul_isUnit_left (y := e' w') ?_
    have h2 : a * c * ((e' u' * e' w' : O) : L) = 1 := by
      rw [← map_mul, ← hej, ← hes, hprod, map_one]
    rcases O.mem_or_inv_mem (a * c) with h | h
    · exact IsUnit.of_mul_eq_one_right (⟨_, h⟩ : O) (Subtype.ext h2)
    · have h3 : u' * w' = (⟨_, h⟩ : O) ⊗ₜ 1 := by
        apply hjinj
        rw [← inv_smul_smul₀ hac (j (u' * w')), hprod]
        simp [hj, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
      have h4 : r (u' * w') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hu' hw'
      have h5 : e' u' * e' w' = ⟨_, h⟩ := by
        rw [← map_mul, h3]; simp [he']
      rw [h5, ← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro h6
      apply h4
      rw [h3, hr, Algebra.TensorProduct.map_tmul]
      change (IsLocalRing.residue O _) ⊗ₜ _ = 0
      rw [h6, TensorProduct.zero_tmul]
  have h7 : a * (e' u' : L) = 1 := by rw [← hej, ← hes, ← eu, h1]
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have hat : a = t := by
    have : (e' u' : L) * t = 1 := by exact_mod_cast congrArg Subtype.val ht
    calc a = a * (e' u' * t) := by rw [this, mul_one]
      _ = t := by rw [← mul_assoc, h7, one_mul]
  obtain ⟨d, hd⟩ := hcu i
  rw [hd, hat]
  exact mul_mem t.2 d.2
end GlobalTheory.UnitRigidity
