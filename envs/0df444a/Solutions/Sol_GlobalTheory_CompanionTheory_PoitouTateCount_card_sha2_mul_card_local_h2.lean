-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PoitouTateCount.card_sha2_mul_card_local_h2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:46.353857+00:00
-- url     : https://prove2.me/submissions/1cedf48c-14b8-4d01-99ac-4f189a2e811a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NatCardDualEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardEqCardKerMulCardRange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDualStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristicStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateNineTermExact
import Theorems.Thm_GlobalTheory_CompanionTheory_Counting_card_eq_card_ker_mul_card_range
import Theorems.Thm_GlobalTheory_CompanionTheory_ZModDual_nat_card_dual_eq
import Theorems.Thm_GlobalTheory_T_finite_local_cohomology_at_places_of_localFiniteness
import Theorems.Thm_GlobalTheory_T_poitou_tate_euler_characteristic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PoitouTateCount
namespace GlobalTheory.CompanionTheory.PoitouTateCount
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → Finite (H2 ρ) → Finite (H0 (twDual μ ρ)) → Nat.card (Sha2 ρ (locFam S Av) (continuous_locFam S Av)) * Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) = Nat.card (H2 ρ) * Nat.card (H0 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hLF hr hAv hNine hH2 hH0
  obtain ⟨_δ₁, _δ₂, -, -, -, -, -, -, -, hex, hsurj⟩ := hNine
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v =>
    (GlobalTheory.T.finite_local_cohomology_at_places_of_localFiniteness F Ω l r M S Av μ ρ hρ hLF hr hAv v).2.2
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
  have hsha : Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) :=
    (GlobalTheory.T.poitou_tate_euler_characteristic F Ω l r M S Av μ ρ hρ).2.2
  have h1 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (loc2 S Av ρ)
  have h2 := GlobalTheory.CompanionTheory.Counting.card_eq_card_ker_mul_card_range (ZMod (l ^ r)) _ _ (tr2 S Av μ j ρ)
  have hker : LinearMap.ker (tr2 S Av μ j ρ) = LinearMap.range (loc2 S Av ρ) := LinearMap.exact_iff.mp hex
  have htop : LinearMap.range (tr2 S Av μ j ρ) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have htopc : Nat.card ↥(⊤ : Submodule (ZMod (l ^ r)) (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ)))) =
      Nat.card (Module.Dual (ZMod (l ^ r)) ↥(H0 (twDual μ ρ))) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  have hD := GlobalTheory.CompanionTheory.ZModDual.nat_card_dual_eq (l ^ r) ↥(H0 (twDual μ ρ))
  rw [hsha, h2, hker, htop, htopc, hD, h1]
  ring
end GlobalTheory.CompanionTheory.PoitouTateCount
