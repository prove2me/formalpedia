-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.exists_of_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:10.611877+00:00
-- url     : https://prove2.me/submissions/6476608c-a964-415c-b5ba-fecd8620049a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_exists_cyclic
import Theorems.Thm_GlobalTheory_ClassParam_mem_UJ_iff
import Theorems.Thm_GlobalTheory_ClassParam_hform_symm
import Theorems.Thm_GlobalTheory_ClassParam_hlin_surj
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_trace_star
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_eq_of_trace
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_exists_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
namespace GlobalTheory.ClassParam
namespace HidaSetting
theorem _root_.solution [IsArtinianRing A] (S : HidaSetting σ τ α b) (hJ : IsHerm σ J)
    (hd : IsUnit J.det) (g : UJ σ J)
    (hg : ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A).charpoly
      = (Algebra.leftMulMatrix b α).charpoly)
    (hs : (Algebra.leftMulMatrix b α).charpoly.Separable) :
    ∃ x φ, IsUnit x ∧ τ x = x ∧ Iso σ τ J x φ ∧
      Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ := by
  set G : Matrix (Fin r) (Fin r) A := ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) with hG
  obtain ⟨v, hv⟩ := exists_cyclic G (hg ▸ hs)
  have hmin : aeval G (minpoly A S.pb.gen) = 0 := by
    rw [← charpoly_leftMulMatrix S.pb]
    show aeval G (Algebra.leftMulMatrix b α).charpoly = 0
    rw [← hg]; exact Matrix.aeval_self_charpoly G
  let ρ := S.pb.lift G hmin
  have hρ : ρ α = G := S.pb.lift_gen G hmin
  let φ₀ : B →ₗ[A] (Fin r → A) :=
    { toFun := fun y => ρ y *ᵥ v
      map_add' := fun y z => by rw [map_add, Matrix.add_mulVec]
      map_smul' := fun a y => by rw [map_smul, Matrix.smul_mulVec]; rfl }
  have hdet : IsUnit (LinearMap.toMatrix b (Pi.basisFun A (Fin r)) φ₀).det := by
    convert hv using 2
    ext i j
    simp [LinearMap.toMatrix_apply, φ₀, S.pow, hρ, krylov]
  let φ := LinearEquiv.ofIsUnitDet hdet
  have hφ : ∀ y, φ y = ρ y *ᵥ v := fun y => LinearEquiv.ofIsUnitDet_apply hdet y
  have hα : ∀ y, φ (α * y) = G *ᵥ φ y := fun y => by
    rw [hφ, hφ, map_mul, hρ, Matrix.mulVec_mulVec]
  have hadj1 : ∀ y y', hform σ J (φ y') (φ (α * y)) = hform σ J (φ (τ α * y')) (φ y) := by
    intro y y'
    rw [← (mem_UJ_iff σ J _).1 g.2 (φ (τ α * y')), ← hα, ← hα, ← mul_assoc, S.hα, one_mul]
  have hadjn : ∀ (n : ℕ) y y',
      hform σ J (φ y') (φ (α ^ n * y)) = hform σ J (φ (τ (α ^ n) * y')) (φ y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y y'
      rw [pow_succ', mul_assoc, hadj1, ih, map_mul τ, ← mul_assoc, mul_comm (τ α)]
  have hadj : ∀ l y y', hform σ J (φ y') (φ (l * y)) = hform σ J (φ (τ l * y')) (φ y) := by
    intro l y y'
    have hl : l ∈ Submodule.span A (Set.range b) := b.mem_span l
    induction hl using Submodule.span_induction with
    | mem l hl => obtain ⟨i, rfl⟩ := hl; rw [S.pow, hadjn]
    | zero => simp [hform]
    | add l m _ _ h1 h2 =>
      rw [add_mul, map_add, map_add, add_mul, map_add]
      simp only [hform, Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
      rw [h1, h2]
    | smul a l _ h1 =>
      have e : τ (a • l) * y' = σ a • (τ l * y') := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, S.comp, mul_assoc]
      rw [smul_mul_assoc, map_smul, e, map_smul]
      have e1 : ∀ u u' : Fin r → A, hform σ J u (a • u') = a * hform σ J u u' := fun u u' =>
        (hlin σ J u).map_smul a u'
      have e2 : ∀ u u' : Fin r → A, hform σ J (σ a • u) u' = a * hform σ J u u' := fun u u' => by
        simp [hform, S.hσ, Finset.mul_sum, mul_assoc]
      rw [e1, e2, h1]
  obtain ⟨x, hx⟩ := S.exists_trace (hlin σ J (φ 1) ∘ₗ φ.toLinearMap)
  have hiso : Iso σ τ J x φ := by
    intro y y'
    have := hadj (τ y') y 1
    rw [S.hτ, mul_one] at this
    rw [← this]
    refine (hx (τ y' * y)).trans ?_
    unfold tf; congr 1; ring
  refine ⟨x, φ, ?_, ?_, hiso, fun u => by rw [hα]; simp⟩
  · obtain ⟨u, hu⟩ := hlin_surj σ S.hσ hd (Algebra.trace A B ∘ₗ φ.symm.toLinearMap)
    refine IsUnit.of_mul_eq_one (τ (φ.symm u)) (S.eq_of_trace fun y => ?_)
    have e1 := hiso y (φ.symm u)
    rw [LinearEquiv.apply_symm_apply, hu] at e1
    unfold tf at e1
    rw [mul_right_comm, ← e1]
    simp
  · refine S.eq_of_trace fun y => ?_
    have e1 := hiso y 1
    rw [hform_symm σ S.hσ hJ, hiso] at e1
    unfold tf at e1
    rw [← S.trace_star] at e1
    simpa [S.hτ] using e1
end HidaSetting
end GlobalTheory.ClassParam
