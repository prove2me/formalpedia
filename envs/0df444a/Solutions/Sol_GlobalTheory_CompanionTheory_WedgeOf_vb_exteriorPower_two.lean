-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:58.509477+00:00
-- url     : https://prove2.me/submissions/74850b6e-6102-4658-a680-f66be2b5649f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRank
import Theorems.Thm_GlobalTheory_TopForm_isBaseChange_exteriorPower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ),
    VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  intro R V _ _ _ g h
  obtain ⟨hf, hp, hr⟩ := h
  have hproj : Module.Projective R (⋀[R]^2 V) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hp
    haveI : Module.Free R (⋀[R]^2 (V →₀ R)) := exteriorPower.instFree R 2
    refine Module.Projective.of_split (exteriorPower.map 2 s)
      (exteriorPower.map 2 (Finsupp.linearCombination R id)) ?_
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hb := LocalizedModule.isBaseChange p.asIdeal.primeCompl V
  have hb2 := GlobalTheory.TopForm.isBaseChange_exteriorPower hb 2
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule p.asIdeal.primeCompl V
  let q : PrimeSpectrum S := IsLocalRing.closedPoint S
  have hq : PrimeSpectrum.comap (algebraMap R S) q = p :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal))
  have h1 := Module.rankAtStalk_isBaseChange hb q
  have h2 := Module.rankAtStalk_isBaseChange hb2 q
  rw [hq] at h1 h2
  haveI : Module.Finite S M := Module.Finite.equiv hb.equiv
  haveI : Module.Flat S M := Module.Flat.of_linearEquiv hb.equiv.symm
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  have h3 : Module.finrank S M = g := by
    rw [← hr p, ← h1, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank S (⋀[S]^2 M) = _
  rw [exteriorPower.finrank_eq, h3]
end GlobalTheory.CompanionTheory.WedgeOf
