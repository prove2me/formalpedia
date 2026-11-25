-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_pow_frob_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:54:40.420389+00:00
-- url     : https://prove2.me/submissions/44d111b6-ab52-4541-8e31-4484dffe5707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_IsSmooth_finite_range
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_pow_eq_pow_of_deg_eq
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ (frob h) ^ m) (ρ σ) := by
  have h1 : ∀ τ : Weil h, ∃ m : ℕ, 0 < m ∧ Commute (ρ (frob h) ^ m) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, he⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob h)
      (τ * frob h * τ⁻¹) (by simp [deg_mul, deg_inv])
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, ← map_pow, conj_pow] at he
    show _ * _ = _ * _
    rw [← map_pow]
    conv_lhs => rw [he]
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h2 : ∀ S : Set (End ℂ V), S.Finite → (∀ x ∈ S, ∃ τ, ρ τ = x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, Commute (ρ (frob h) ^ m) x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert x S _ _ ih =>
      intro hx
      obtain ⟨m, hm, hc⟩ := ih fun y hy => hx y (Set.mem_insert_of_mem _ hy)
      obtain ⟨τ, rfl⟩ := hx x (Set.mem_insert _ _)
      obtain ⟨n, hn, hc'⟩ := h1 τ
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      rintro y (rfl | hy)
      · rw [mul_comm, pow_mul]; exact hc'.pow_left m
      · rw [pow_mul]; exact (hc y hy).pow_left n
  obtain ⟨m, hm, hc⟩ := h2 _ hρ.finite_range (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)
  refine ⟨m, hm, fun σ => ?_⟩
  have h0 : deg ((frob h ^ deg σ)⁻¹ * σ) = 0 := by
    simp [deg_mul, deg_inv, deg_zpow, deg_frob]
  have h3 : Commute (ρ (frob h) ^ m) (ρ ((frob h ^ deg σ)⁻¹ * σ)) :=
    hc _ ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have h4 : Commute (ρ (frob h) ^ m) (ρ (frob h ^ deg σ)) :=
    (((Commute.refl (frob h)).zpow_right _).map ρ).pow_left m
  have := h4.mul_right h3
  rwa [← map_mul, mul_inv_cancel_left] at this
end GlobalTheory.WeilDeligne
