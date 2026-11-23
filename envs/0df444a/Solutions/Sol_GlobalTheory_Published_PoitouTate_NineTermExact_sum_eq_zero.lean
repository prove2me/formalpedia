-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTate.NineTermExact.sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:59.320225+00:00
-- url     : https://prove2.me/submissions/f6306896-cc37-44e3-8f83-36608998a1fc

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Theorems.Thm_GlobalTheory_Published_PoitouTate_poitouTateNineTerm_transgressionTwo_apply

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
namespace NineTermExact
theorem _root_.solution {hρ : ContAction (charRep μ)}
    (h : NineTermExact S Av μ j (charRep μ) hρ) (x : H2 (charRep μ)) :
    ∑ v : S, j v (resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) x) = 0 := by
  obtain ⟨δ₁, δ₂, -, -, -, -, -, -, -, h8, -⟩ := h

  have key : ∀ (v : S) (c : H2 ((charRep μ).comp (locFam S Av v))),
      cup20 μ (charRep μ) (locFam S Av v) c
        (resH0 (twDual μ (charRep μ)) (locFam S Av v) (idInv μ)) = c := by
    intro v c
    refine Submodule.Quotient.induction_on _ c fun z => ?_
    simp only [cup20, cupProductH2H0, Submodule.liftQ_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply]

    congr 1

  have hz : tr2 S Av μ j (charRep μ) (loc2 S Av (charRep μ) x) = 0 := (h8 _).2 ⟨x, rfl⟩
  have hz' := LinearMap.congr_fun hz (idInv μ)
  simp only [poitouTateNineTerm_transgressionTwo_apply, loc2, LinearMap.pi_apply, key, LinearMap.zero_apply] at hz'
  exact hz'
end NineTermExact
end GlobalTheory.Published.PoitouTate
