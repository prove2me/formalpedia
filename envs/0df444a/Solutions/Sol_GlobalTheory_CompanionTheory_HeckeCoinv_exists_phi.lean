-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.exists_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:10.872854+00:00
-- url     : https://prove2.me/submissions/18580430-9070-4daa-8c38-70bf01c60d09

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_cnt_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_cnt_self_pos
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution [Finite (MulAction.orbitRel.Quotient Γ X)] [∀ x : X, Finite (MulAction.stabilizer Γ x)] :
    ∃ (N : ℕ) (φ : (X →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)), Function.Surjective φ ∧
      ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ) := by
  classical
  let Q := MulAction.orbitRel.Quotient Γ X
  let π : X → Q := fun x => Quotient.mk'' x
  let o : Q → X := fun q => q.out
  have hπo : ∀ q, π (o q) = q := fun q => Quotient.out_eq' q
  have hrel : ∀ x y, π x = π y → ∃ γ : Γ, γ • y = x := by
    intro x y hxy
    have : x ∈ MulAction.orbit Γ y := MulAction.orbitRel_apply.1 (Quotient.eq''.1 hxy)
    exact this
  let e : Q ≃ Fin (Nat.card Q) := Finite.equivFin Q
  let w : Q → ℕ := fun q => cnt Γ (o q) (o q)
  have hw : ∀ q, 0 < w q := fun q => cnt_self_pos _
  let cf : Q → ℂ := fun q => ((Real.sqrt (w q) : ℝ) : ℂ)
  have hcf : ∀ q, conj (cf q) * cf q = (w q : ℂ) := by
    intro q
    simp only [cf, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hcf0 : ∀ q, cf q ≠ 0 := by
    intro q
    have := Real.sqrt_pos.2 (Nat.cast_pos.2 (hw q) : (0 : ℝ) < w q)
    exact Complex.ofReal_ne_zero.2 this.ne'
  let vec : X → EuclideanSpace ℂ (Fin (Nat.card Q)) := fun x => EuclideanSpace.single (e (π x)) (cf (π x))
  refine ⟨Nat.card Q, Finsupp.linearCombination ℂ vec, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, eq_top_iff]
    intro v _
    rw [← (EuclideanSpace.basisFun (Fin (Nat.card Q)) ℂ).sum_repr v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    refine ⟨Finsupp.single (o (e.symm i)) (cf (e.symm i))⁻¹, ?_⟩
    simp only [Finsupp.linearCombination_single, vec, hπo, Equiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hcf0]
    · simp [hj]
  · intro x y
    simp only [Finsupp.linearCombination_single, one_smul, vec]
    by_cases hxy : π x = π y
    · obtain ⟨γ, hγ⟩ := hrel (o (π x)) x (hπo _ ▸ rfl)
      obtain ⟨γ', hγ'⟩ := hrel (o (π x)) y (by rw [hπo, hxy])
      have : cnt Γ x y = w (π x) := by
        show _ = cnt Γ (o (π x)) (o (π x))
        conv_rhs => rw [← hγ]
        conv_rhs => rhs; rw [hγ, ← hγ']
        exact cnt_congr γ γ'
      rw [this, ← hxy, EuclideanSpace.inner_single_left]
      simp [hcf]
    · have hne : e (π x) ≠ e (π y) := fun h => hxy (e.injective h)
      have : IsEmpty {γ : Γ // γ • x = y} := ⟨fun γ => by
        obtain ⟨γ, hγ⟩ := γ
        apply hxy
        rw [← hγ]
        exact (Quotient.eq''.2 (MulAction.orbitRel_apply.2 ⟨γ⁻¹, by simp⟩))⟩
      have h0 : cnt Γ x y = 0 := Nat.card_of_isEmpty
      rw [h0, EuclideanSpace.inner_single_left]
      simp [hne, Ne.symm hne]
end GlobalTheory.CompanionTheory.HeckeCoinv
