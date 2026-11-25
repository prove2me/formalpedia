-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:25.7601+00:00
-- url     : https://prove2.me/submissions/f685da59-c7a6-43f3-bc5b-1901f13f51d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_hasFiniteLength_coinv_of_ker
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_indSnd_inr
import Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_hasFiniteLength_of_finiteDimensional
import Theorems.Thm_GlobalTheory_SmGL_IndCoinv_smInd_coinvariants
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_isSmooth
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_surjective
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_LeviInt_levi_integral_facts
import Theorems.Thm_GlobalTheory_SmGL_exists_open_normalised_subgroup_subset
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_twist
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  intro k _ _ _ _ hI Γ W b c d _ _ _ _ _ _ _ _ _ e τ hτ ψ hfin
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ b _ (two e)
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two c d)) W :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k c d).symm.toMonoidHom
  let R : Submodule ℂ W := twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ
  have hR : ∀ (m : Levi k (Two c d)) (v : W), v ∈ R → ρ m v ∈ R :=
    fun m v hv => twRel_stable τ ψ _ v hv
  let ρD : Representation ℂ (Levi k (Two c d)) (W ⧸ R) := Representation.quotient ρ R hR
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := R.mkQ, isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective R
  have hρ : IsSmooth ρ := isSmooth_comp hτ _
    ((continuous_apply false).prodMk (continuous_apply true))
  have hρD : IsSmooth ρD := (IsSubquotient.of_surjective q hq).isSmooth hρ
  haveI : FiniteDimensional ℂ (W ⧸ R) := hfin
  have hInd : HasFiniteLength (parInd (two e) ρD) :=
    hI Bool b (Two c d) (two e) (W ⧸ R) ρD hρD
      (FinitenessModel.hasFiniteLength_of_finiteDimensional ρD)
  let σ : Representation ℂ (parab k (two e)) W :=
    (twist ρ (deltaHalf k (Two c d))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : σ.IntertwiningMap ((twist ρD (deltaHalf k (Two c d))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → σ.IntertwiningMap σ := fun γ =>
    { toLinearMap := (ψ γ : ℂ)⁻¹ • τ (γ, 1)
      isIntertwining' := fun p => by
        have h := (compMap (twistMap (actFst τ γ) (deltaHalf k (Two c d))) (leviProj k (two e))).isIntertwining' p
        have h' : τ (γ, 1) ∘ₗ σ p = σ p ∘ₗ τ (γ, 1) := h
        rw [LinearMap.smul_comp, LinearMap.comp_smul, h'] }
  have hT : ∀ γ v, T γ v = (ψ γ : ℂ)⁻¹ • τ (γ, 1) v := fun _ _ => rfl
  have hψ : ∀ γ, (ψ γ : ℂ) ≠ 0 := fun γ => (ψ γ).ne_zero
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have hxR : x ∈ R := (Submodule.Quotient.mk_eq_zero R).1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y : W | ∃ γ z, y = T γ z - z})).2 ?_ hxR
    rintro _ ⟨γ, v, rfl⟩
    have h : (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) γ v - (ψ γ : ℂ) • v =
        (ψ γ : ℂ) • (T γ v - v) := by
      rw [hT, smul_sub, smul_smul, mul_inv_cancel₀ (hψ γ), one_smul]
      rfl
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL b k) (parab k (two e)) (KO k b) hP
    SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k b) W (W ⧸ R) σ _ hσ
    α Γ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  refine hasFiniteLength_coinv_of_ker (indSnd e τ) ψ (parInd (two e) ρD) Φ.toLinearMap
    (fun g f => ?_) (le_antisymm ?_ ?_) hInd
  · rw [indSnd_inr]
    exact Φ.isIntertwining _ _ g f
  · intro f hf
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl Γ (GL b k))) ψ)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    have h : smIndMap (T γ) z - z = (ψ γ : ℂ)⁻¹ • (indSnd e τ (γ, 1) z - (ψ γ : ℂ) • z) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (hψ γ), one_smul]
      congr 1
      refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      show (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 x) = (ψ γ : ℂ)⁻¹ • τ (γ, 1) (z.1.1 (x * 1))
      rw [mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, z, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, f, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have h : τ (γ, 1) (f.1.1 x) - (ψ γ : ℂ) • f.1.1 x ∈ R :=
      Submodule.subset_span ⟨γ, f.1.1 x, rfl⟩
    have h2 := (Submodule.Quotient.mk_eq_zero R).2 h
    show q (τ (γ, 1) (f.1.1 (x * 1)) - (ψ γ : ℂ) • f.1.1 x) = 0
    rw [mul_one]
    exact h2
end GlobalTheory.CompanionTheory.ThetaGLLen
