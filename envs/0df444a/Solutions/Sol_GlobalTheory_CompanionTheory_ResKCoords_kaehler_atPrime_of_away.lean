-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.kaehler_atPrime_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:58.844605+00:00
-- url     : https://prove2.me/submissions/b9e9b23c-5c68-475a-809a-8c24802b1b9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SmoothLocalRingFreeDifferentials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
namespace GlobalTheory.CompanionTheory.ResKCoords
theorem _root_.solution (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp
end GlobalTheory.CompanionTheory.ResKCoords
