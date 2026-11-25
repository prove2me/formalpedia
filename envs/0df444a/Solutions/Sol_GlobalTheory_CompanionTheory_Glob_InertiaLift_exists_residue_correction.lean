-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.InertiaLift.exists_residue_correction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:21.705684+00:00
-- url     : https://prove2.me/submissions/2831410d-3c71-438a-9809-4997d4aae239

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
import Theorems.Thm_ReciprocityTheory_Gal_under_primeBelow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.InertiaLift
variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
namespace GlobalTheory.CompanionTheory.Glob.InertiaLift
theorem _root_.solution [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    (w : HeightOneSpectrum (𝓞 K))
    (hA : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal)
    {σ₁ : Ω ≃ₐ[F] Ω} (hd : σ₁ ∈ Dec (F := F) A)
    (hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1) :
    ∃ h : Ω ≃ₐ[K] Ω, h • A = A ∧ ∀ b : IntCl K Ω, A.valuation (h (b : Ω) - σ₁ b) < 1 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : IsGalois K Ω := {}
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set P := primeBelow (F := K) A with hPdef
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : P.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) P
    (by rw [show Ideal.comap (algebraMap (𝓞 K) (IntCl K Ω)) P = w.asIdeal from
      under_primeBelow hA]; exact w.isMaximal)
  let e : IntCl K Ω ≃+* IntCl K Ω := actInt σ₁
  have hP : P = P.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hd) _).symm
  let φr : (IntCl K Ω ⧸ P) ≃+* (IntCl K Ω ⧸ P) := Ideal.quotientEquiv P P e hP
  let φ : (IntCl K Ω ⧸ P) ≃ₐ[𝓞 K ⧸ w.asIdeal] (IntCl K Ω ⧸ P) := AlgEquiv.ofRingEquiv (f := φr) (by
    intro r
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
    show φr (Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)) =
      Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)
    rw [Ideal.quotientEquiv_mk]
    refine Ideal.Quotient.eq.2 ?_
    exact hz z)
  obtain ⟨⟨h, hhP⟩, hh⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) w.asIdeal P φ
  have hhP' : h • P = P := hhP
  refine ⟨h, ?_, fun b => ?_⟩
  · refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (h • A) ↔ b' ∈ P
    rw [primeBelow_smul, hhP']
  · have h1 : Ideal.Quotient.mk P (h • b) = Ideal.Quotient.mk P (e b) :=
      DFunLike.congr_fun hh (Ideal.Quotient.mk P b)
    exact Ideal.Quotient.eq.1 h1
end GlobalTheory.CompanionTheory.Glob.InertiaLift
