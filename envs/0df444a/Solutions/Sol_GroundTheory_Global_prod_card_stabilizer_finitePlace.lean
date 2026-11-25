-- Prove2me | solution 1 for GroundTheory.Global.prod_card_stabilizer_finitePlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:45.66094+00:00
-- url     : https://prove2.me/submissions/179f568d-75f2-4830-8771-36c37124c414

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Theorems.Thm_GroundTheory_Global_eq_placeBelow_of_liesOver
import Theorems.Thm_GroundTheory_Global_placeBelow_smul
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_coeff_permOfFun
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.coeff_permOfFun
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L)))
namespace GroundTheory.Global
theorem _root_.solution (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    letI := stableMulAction S hS
    ∀ [Fintype (orbitRel.Quotient (L ≃ₐ[K] L) S)],
    ∏ ω : orbitRel.Quotient (L ≃ₐ[K] L) S,
        (Nat.card (stabilizer (L ≃ₐ[K] L) (Quotient.out ω)) : ℚ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal),
        ((v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) : ℕ) : ℚ) := by
  let := stableMulAction S hS
  intro _
  have hstab : ∀ x : S, Nat.card (stabilizer (L ≃ₐ[K] L) x) =
      (placeBelow (K := K) x.1).asIdeal.ramificationIdxIn (𝓞 L) *
        (placeBelow (K := K) x.1).asIdeal.inertiaDegIn (𝓞 L) := by
    intro x
    have h1 : stabilizer (L ≃ₐ[K] L) x = stabilizer (L ≃ₐ[K] L) x.1.asIdeal := by
      ext g
      rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff]
      exact ⟨fun h => congrArg HeightOneSpectrum.asIdeal h, fun h => HeightOneSpectrum.ext h⟩
    rw [h1]
    exact Ideal.card_stabilizer_eq (placeBelow (K := K) x.1).asIdeal x.1.asIdeal
  rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
  refine finprod_mem_eq_of_bijOn (fun ω => placeBelow (K := K) (Quotient.out ω).1) ⟨?_, ?_, ?_⟩
    fun ω _ => by rw [hstab]
  · intro ω _
    exact ⟨(Quotient.out ω).1, (Quotient.out ω).2, inferInstance⟩
  · intro ω₁ _ ω₂ _ h
    simp only at h
    set x₁ := Quotient.out ω₁
    set x₂ := Quotient.out ω₂
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L)
      (⟨x₂.1, inferInstance⟩ : SemiLocal.PlacesOver L (placeBelow (K := K) x₂.1))
      ⟨x₁.1, by rw [← h]; infer_instance⟩
    rw [← Quotient.out_eq ω₁, ← Quotient.out_eq ω₂]
    have hg' : g • x₂.1 = x₁.1 := congrArg Subtype.val hg
    exact Quotient.sound ⟨g, Subtype.ext hg'⟩
  · rintro v ⟨w, hw, hlies⟩
    refine ⟨Quotient.mk _ ⟨w, hw⟩, Set.mem_univ _, ?_⟩
    obtain ⟨g, hg⟩ : Quotient.out (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩) ∈
        orbit (L ≃ₐ[K] L) (⟨w, hw⟩ : S) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel (L ≃ₐ[K] L) S) ⟨w, hw⟩))
    simp only
    rw [← hg]
    change placeBelow (g • w) = v
    rw [placeBelow_smul, ← eq_placeBelow_of_liesOver hlies]
end GroundTheory.Global
