-- Prove2me | solution 1 for GlobalTheory.DegreeOne.surjective_of_unique_injective_localHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:40:57.408953+00:00
-- url     : https://prove2.me/submissions/c211b657-cdd2-41c1-b253-301ec8578011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveFiniteOfUniqueEmbeddingCompleteNormal
import Theorems.Thm_GlobalTheory_CompleteFiniteExtension_isAdicComplete_of_finite_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isLocalRing_finite_domain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DegreeOne
namespace GlobalTheory.DegreeOne
theorem _root_.solution : ∀ (B R : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ψ : B →+* R), IsAdicComplete (maximalIdeal B) B → Function.Injective ψ → ψ.Finite → (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [CharZero R'], IsAdicComplete (maximalIdeal R') R' → ∀ f g : R →+* R', Function.Injective f → Function.Injective g → IsLocalHom f → IsLocalHom g → f.comp ψ = g.comp ψ → f = g) → Function.Surjective ψ := by
  intro B R _ _ _ _ _ _ _ _ _ ψ hB hinj hfin huniq
  haveI := hB
  letI : Algebra B R := ψ.toAlgebra
  haveI : Module.Finite B R := hfin
  haveI : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  haveI : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).2 hinj
  haveI : CharZero B := ⟨fun m n h => Nat.cast_injective (R := R) (by simpa only [map_natCast] using congrArg ψ h)⟩
  let K := FractionRing B
  let M := FractionRing R
  have hBM : Function.Injective (algebraMap B M) := by
    rw [IsScalarTower.algebraMap_eq B R M]
    exact (IsFractionRing.injective R M).comp hinj
  haveI : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).2 hBM
  letI : Algebra K M := FractionRing.liftAlgebra B M
  haveI : IsScalarTower B K M := FractionRing.isScalarTower_liftAlgebra B M
  haveI : Module.Finite K M := Module.Finite.of_isLocalization B R (Rₚ := K) (Sₚ := M) (nonZeroDivisors B)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing B (K := K)
  let Ω := AlgebraicClosure M
  let L := IntermediateField.normalClosure K M Ω
  haveI : FiniteDimensional K L := normalClosure.is_finiteDimensional K M Ω
  haveI : IsScalarTower B K Ω := inferInstance
  haveI : IsScalarTower B K L := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let C := integralClosure B L
  haveI : Module.Finite B C := IsIntegralClosure.finite B K L C
  haveI : IsLocalRing C := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := B) C
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  haveI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  haveI : CharZero C := ⟨fun m n h => Nat.cast_injective (R := L) (by simpa using congrArg Subtype.val h)⟩
  have hCc : IsAdicComplete (maximalIdeal C) C := CompleteFiniteExtension.isAdicComplete_of_finite_local B C

  have hK : ∀ b : B, algebraMap K L (algebraMap B K b) = algebraMap B L b := fun b =>
    (IsScalarTower.algebraMap_apply B K L b).symm
  have key : ∀ σ : M →ₐ[K] Ω, ∃ f : R →+* C, Function.Injective f ∧ IsLocalHom f ∧ f.comp ψ = algebraMap B C ∧
      ∀ r, ((f r : L) : Ω) = σ (algebraMap R M r) := by
    intro σ
    have hmem : ∀ x, (σ.toRingHom.comp (algebraMap R M)) x ∈ L := fun x =>
      σ.fieldRange_le_normalClosure ⟨_, rfl⟩
    let g₀ : R →+* L := (σ.toRingHom.comp (algebraMap R M)).codRestrict L hmem
    have hg₀ : ∀ b, g₀ (algebraMap B R b) = algebraMap B L b := by
      intro b
      apply Subtype.val_injective
      show σ (algebraMap R M (algebraMap B R b)) = _
      rw [← IsScalarTower.algebraMap_apply B R M, IsScalarTower.algebraMap_apply B K M, σ.commutes,
        ← hK]
      rfl
    let g : R →ₐ[B] L := { g₀ with commutes' := hg₀ }
    have hC : ∀ r, g r ∈ C := fun r => (Algebra.IsIntegral.isIntegral (R := B) r).map g
    let f : R →+* C := (g : R →+* L).codRestrict C hC
    have hcomm : f.comp ψ = algebraMap B C := by
      ext b
      exact congrArg Subtype.val (hg₀ b)
    have hfinj : Function.Injective f := fun x y h =>
      IsFractionRing.injective R M (σ.injective (congrArg (fun c : C => ((c : L) : Ω)) h))
    have hfi : f.IsIntegral := by
      letI : Algebra R C := f.toAlgebra
      haveI : IsScalarTower B R C := IsScalarTower.of_algebraMap_eq' hcomm.symm
      intro c
      exact (integralClosure.isIntegral c).tower_top
    exact ⟨f, hfinj, RingHom.IsIntegral.isLocalHom hfi hfinj, hcomm, fun r => rfl⟩
  choose f hfi hfl hfc hfv using key
  have hemb : ∀ σ τ : M →ₐ[K] Ω, σ = τ := by
    intro σ τ
    have h := huniq C hCc (f σ) (f τ) (hfi σ) (hfi τ) (hfl σ) (hfl τ) ((hfc σ).trans (hfc τ).symm)
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R) (S := M)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
    rw [← hfv σ r, ← hfv τ r, h]
  have hrank : Module.finrank K M = 1 := by
    rw [← Field.finSepDegree_eq_finrank_of_isSeparable K M]
    unfold Field.finSepDegree
    haveI : Subsingleton (Field.Emb K M) := ⟨hemb⟩
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨IsAlgClosed.lift⟩⟩
  have hbot : (⊥ : Subalgebra K M) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hrank
  intro r
  obtain ⟨k, hk⟩ := Algebra.mem_bot.1 (hbot.symm ▸ Algebra.mem_top : algebraMap R M r ∈ (⊥ : Subalgebra K M))
  have hki : IsIntegral B k := by
    have h1 : IsIntegral B (algebraMap K M k) := hk ▸
      (Algebra.IsIntegral.isIntegral (R := B) r).map (IsScalarTower.toAlgHom B R M)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B K M) (algebraMap K M).injective).1 h1
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hki
  refine ⟨b, IsFractionRing.injective R M ?_⟩
  rw [← hk, ← IsScalarTower.algebraMap_apply B K M, IsScalarTower.algebraMap_apply B R M]
  rfl
end GlobalTheory.DegreeOne
