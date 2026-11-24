-- Prove2me | solution 1 for GlobalTheory.ClassParam.classParamAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:32:26.801594+00:00
-- url     : https://prove2.me/submissions/19ef7746-37c0-4417-a7ec-5dabaa0efbfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_exists_intw
import Theorems.Thm_GlobalTheory_ClassParam_isConj_of_iso
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_norm_of_isConj
import Theorems.Thm_GlobalTheory_ClassParam_charpoly_of_intw
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_exists_of_charpoly
import Theorems.Thm_GlobalTheory_ClassParam_trLk_eq
import Theorems.Thm_GlobalTheory_ClassParam_exists_pow_basis
import Theorems.Thm_GlobalTheory_ClassParam_exists_setting
import Theorems.Thm_GlobalTheory_ClassParam_exists_unit_plus
import Theorems.Thm_GlobalTheory_ClassParam_mk_eq_iff_normL

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
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) : ClassParamAt k hP := by
  classical
  intro J hJ hd
  obtain ⟨b, S, hch⟩ := exists_setting k hP hc
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  haveI : IsArtinianRing (k ⊗[F] E) := IsArtinianRing.of_finite k _
  haveI : IsArtinianRing (E ⊗[F] k) :=
    (Algebra.TensorProduct.comm F k E).toRingEquiv.isArtinianRing
  have hiso : ∀ x φ, IsIsometry hP J x φ ↔
      Iso (sigR (c : E →ₐ[F] E) k) (starLk k hP) J (inclPlus k hP x) φ := by
    intro x φ
    simp only [IsIsometry, Iso, hU, hx, tf, trLk_eq k b₀]
  let Rel : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → UJ (sigR (c : E →ₐ[F] E) k) J → Prop := fun ξ g =>
    ∃ x φ, QuotientGroup.mk x = ξ ∧ IsIsometry hP J x φ ∧
      Intw (AdjoinRoot.root P ⊗ₜ[F] (1 : k))
        ((g : GL (Fin r) (E ⊗[F] k)) : Matrix (Fin r) (Fin r) (E ⊗[F] k)) φ
  have hRel : ∀ ξ ξ' g g', Rel ξ g → Rel ξ' g' →
      (ξ = ξ' ↔ ConjClasses.mk g = ConjClasses.mk g') := by
    rintro _ _ g g' ⟨x, φ, rfl, h1, h2⟩ ⟨x', φ', rfl, h1', h2'⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, mk_eq_iff_normL]
    rw [hiso] at h1 h1'
    constructor
    · rintro ⟨z, hz⟩
      rw [hz] at h1'
      exact isConj_of_iso (h1.mul z) h1' (h2.mul z) h2'
    · intro h
      exact S.norm_of_isConj h1 h1' h2 h2' h.symm
  let Φ : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → ConjClasses (UJ (sigR (c : E →ₐ[F] E) k) J) :=
    fun ξ => if h : ∃ g, Rel ξ g then ConjClasses.mk h.choose else ConjClasses.mk 1
  have hΦ : ∀ ξ g, Rel ξ g → Φ ξ = ConjClasses.mk g := by
    intro ξ g h
    have h' : ∃ g, Rel ξ g := ⟨g, h⟩
    simp only [Φ, dif_pos h']
    exact (hRel _ _ _ _ h'.choose_spec h).1 rfl
  have hex : ∀ ξ ∈ Xk hP J, ∃ g, Rel ξ g := by
    rintro _ ⟨x, rfl, φ, h⟩
    obtain ⟨g, hg⟩ := S.exists_intw ((hiso x φ).1 h)
    exact ⟨g, x, φ, rfl, h, hg⟩
  refine ⟨?_, Φ, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨x', hx', φ, h⟩
    obtain ⟨z, hz⟩ := (mk_eq_iff_normL k hP _ _).1 hx'
    exact ⟨_, (hiso _ _).2 (hz ▸ ((hiso _ _).1 h).mul z)⟩
  · intro x φ h
    obtain ⟨g, hg⟩ := S.exists_intw ((hiso x φ).1 h)
    exact ⟨g, hg, hΦ _ _ ⟨x, φ, rfl, h, hg⟩⟩
  · intro ξ hξ
    obtain ⟨g, hg⟩ := hex ξ hξ
    refine ⟨g, (hΦ _ _ hg).symm, ?_⟩
    obtain ⟨x, φ, -, -, h⟩ := hg
    rw [charpoly_of_intw b h, hch]
  · intro ξ hξ ξ' hξ' h
    obtain ⟨g, hg⟩ := hex ξ hξ
    obtain ⟨g', hg'⟩ := hex ξ' hξ'
    rw [hΦ _ _ hg, hΦ _ _ hg'] at h
    exact (hRel _ _ _ _ hg hg').2 h
  · rintro _ ⟨g, rfl, hg⟩
    obtain ⟨x, φ, hu, hx, h1, h2⟩ := S.exists_of_charpoly hJ hd g (hg.trans hch.symm)
      (by rw [hch]; exact hP.2.1.separable.map)
    obtain ⟨x₀, rfl⟩ := exists_unit_plus k hP hu hx
    have h3 := (hiso _ _).2 h1
    exact ⟨QuotientGroup.mk x₀, ⟨x₀, rfl, φ, h3⟩, hΦ _ _ ⟨x₀, φ, rfl, h3, h2⟩⟩
end GlobalTheory.ClassParam
