-- Prove2me | solution 1 for GlobalTheory.AdLat.Complete.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:11.820468+00:00
-- url     : https://prove2.me/submissions/64bc868f-fcf3-4c63-bd69-fba4367a2c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
import Theorems.Thm_GlobalTheory_AdLat_Complete_baer_fractionField
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Complete
namespace GlobalTheory.AdLat.Complete
theorem _root_.solution (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) [Module.Finite R M] :
    ∃ (m : ℕ) (e : Fin m → V) (t : Fin m → (V →ₗ[K] K)), (∀ i, e i ∈ M) ∧
      (∀ i, ∀ v ∈ M, t i v ∈ (algebraMap R K).range) ∧ ∀ v ∈ M, ∑ i, t i v • e i = v := by
  classical
  have : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R K V
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite _ _
  have : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have h : ∀ i, ∃ s : V →ₗ[R] K, s ∘ₗ M.subtype = Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g :=
    fun i => (baer_fractionField R K).extension_property _ M.injective_subtype _
  choose s hs using h
  have hs' : ∀ i v (hv : v ∈ M), s i v = algebraMap R K (g ⟨v, hv⟩ i) := fun i v hv =>
    LinearMap.congr_fun (hs i) ⟨v, hv⟩
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (s i).extendScalarsOfIsLocalization R⁰ K,
    fun i => (f _).2, fun i v hv => ⟨_, (hs' i v hv).symm⟩, fun v hv => ?_⟩
  have h1 : f (g ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hfg _
  have h2 : ∑ i, g ⟨v, hv⟩ i • f (Pi.single i 1) = ⟨v, hv⟩ := by
    conv_rhs => rw [← h1, pi_eq_sum_univ' (g _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  have h3 := congrArg Subtype.val h2
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h3
  rw [LinearMap.extendScalarsOfIsLocalization_apply', hs' i v hv, algebraMap_smul]
end GlobalTheory.AdLat.Complete
