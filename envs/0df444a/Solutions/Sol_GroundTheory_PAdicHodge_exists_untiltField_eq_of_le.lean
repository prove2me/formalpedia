-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_untiltField_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:11:55.624695+00:00
-- url     : https://prove2.me/submissions/fe22598f-b3d9-479e-91fd-740dc071ec6b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Theorems.Thm_GroundTheory_PAdicHodge_untiltAutHom_bijective
import Theorems.Thm_GroundTheory_PAdicHodge_coe_untiltAut_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] (L : IntermediateField K C) (hL : L ≤ untiltField K C p N) :
    ∃ M : IntermediateField K♭ C♭, M ≤ N ∧ FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  classical
  obtain ⟨hbij, hgal⟩ := untiltAutHom_bijective (K := K) (C := C) (p := p) N
  set F := untiltField K C p N
  set Φ := untiltAutHom (K := K) (C := C) (p := p) N
  set L' : IntermediateField K F := IntermediateField.restrict hL
  set H := L'.fixingSubgroup
  set J := H.comap Φ
  set M0 : IntermediateField K♭ N := IntermediateField.fixedField J
  set M : IntermediateField K♭ C♭ := M0.map N.val
  have hMN : M ≤ N := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hMfin : FiniteDimensional K♭ M :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap M0 N.val).toLinearEquiv
  refine ⟨M, hMN, hMfin, ?_⟩

  have hle : untiltField K C p M ≤ L := by
    rw [untiltField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, ⟨u, rfl⟩, rfl⟩
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono hMN)) u
    have hz : ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : normInteger C) =
        WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u') := by
      simp only [RingHom.comp_apply, u']
      congr 1
    have hzF : ((WittVector.fontaineTheta (normInteger C) p
        (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈ F :=
      coe_mem_untiltField ⟨u', rfl⟩
    change ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : C) ∈ L
    rw [hz]
    have hfix : (⟨_, hzF⟩ : F) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      have hσ : σ ∈ J := hτ
      apply Subtype.ext

      have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
          (u'.coeff n) = u'.coeff n := by
        intro n
        set c := u'.coeff n
        have hcM : algebraMap 𝒪C♭ C♭ (c : 𝒪C♭) ∈ M := (u.coeff n).2
        obtain ⟨y, hy, hyc⟩ := hcM
        have hyfix : σ y = y := (IntermediateField.mem_fixedField_iff J y).1 hy σ hσ
        apply Subtype.ext
        apply IsFractionRing.injective 𝒪C♭ C♭
        rw [algebraMap_integerTiltHom]
        have : (⟨algebraMap 𝒪C♭ C♭ (c : 𝒪C♭), c.2⟩ : N) = y := Subtype.ext hyc.symm
        rw [this]
        change ((σ y : N) : C♭) = _
        rw [hyfix]
        exact hyc
      have hmap : WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ))
          u' = u' := WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
      change ((untiltAut N σ ⟨_, hzF⟩ : F) : C) = _
      rw [coe_untiltAut_fontaineTheta, hmap]
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    exact (IntermediateField.mem_restrict hL _).1 hfix

  have hL'fin : FiniteDimensional K L' := inferInstance
  have hcard : Nat.card J = Nat.card H := by
    refine Nat.card_congr (Equiv.ofBijective (fun σ : J => (⟨Φ σ, σ.2⟩ : H)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hbij.1 (congrArg Subtype.val hab))
    · rintro ⟨τ, hτ⟩
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      exact ⟨⟨σ, hτ⟩, rfl⟩
  have hN : Module.finrank K♭ M0 * Nat.card J = Module.finrank K♭ N := by
    rw [← IntermediateField.finrank_fixedField_eq_card, Module.finrank_mul_finrank]
  have hF : Module.finrank K L' * Nat.card H = Module.finrank K F := by
    have h := IntermediateField.finrank_fixedField_eq_card H
    rw [IsGalois.fixedField_fixingSubgroup] at h
    rw [← h, Module.finrank_mul_finrank]
  have hFN : Module.finrank K F = Module.finrank K♭ N := finrank_untiltField N
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hL'M0 : Module.finrank K L' = Module.finrank K♭ M0 := by
    have := hF.trans (hFN.trans hN.symm)
    rw [hcard] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hLL' : Module.finrank K L = Module.finrank K L' :=
    (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.finrank_eq
  have hMM0 : Module.finrank K♭ M = Module.finrank K♭ M0 :=
    (IntermediateField.equivMap M0 N.val).toLinearEquiv.finrank_eq.symm
  have : FiniteDimensional K L :=
    LinearEquiv.finiteDimensional
      (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.symm
  exact IntermediateField.eq_of_le_of_finrank_le hle
    (by rw [finrank_untiltField, hMM0, ← hL'M0, hLL'])
end GroundTheory.PAdicHodge
