-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.exists_lift_cycMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:14:10.450686+00:00
-- url     : https://prove2.me/submissions/419ea09b-6616-42df-83dd-6b7c6f54b874

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_continuous_cycMod
import Theorems.Thm_ReciprocityTheory_Gal_cyc_eq_map_cycZ
import Theorems.Thm_ReciprocityTheory_Gal_cyc_eq_one_of_mem_Ine
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.PoitouTate
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
variable (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
variable {S Av μ j ρ}
namespace GlobalTheory.Published.PoitouTate
theorem _root_.solution (hS : ContainsAbove S l) :
    ∃ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      μ.comp (toGS Ω _) = cycMod F Ω l r := by
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic

  have hker : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ (cycMod F Ω l r).ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) ?_
    · intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσA⟩ := hσ
      have hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := fun h => hv (hS v h)
      have h1 : cyc F Ω l σ = 1 := cyc_eq_one_of_mem_Ine hl hA (mem_Ine.2 hσA)
      rw [cyc_eq_map_cycZ] at h1
      have h3 := congrArg Units.val h1
      rw [Units.coe_map, Units.val_one] at h3
      have hinj : Function.Injective
          ((algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom) :=
        (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp fun a b h => PadicInt.ext h
      have h2 : cycZ F Ω l σ = 1 := by
        refine Units.ext (hinj ?_)
        rw [Units.val_one, map_one]
        exact h3
      rw [SetLike.mem_coe, MonoidHom.mem_ker, cycMod, MonoidHom.comp_apply, h2, map_one]
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage continuous_cycMod
  refine ⟨QuotientGroup.lift _ (cycMod F Ω l r) hker, MonoidHom.ext fun σ => ?_⟩
  exact QuotientGroup.lift_mk _ hker σ
end GlobalTheory.Published.PoitouTate
