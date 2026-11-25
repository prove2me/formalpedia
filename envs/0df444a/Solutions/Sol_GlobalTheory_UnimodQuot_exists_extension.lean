-- Prove2me | solution 1 for GlobalTheory.UnimodQuot.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:33:58.2999+00:00
-- url     : https://prove2.me/submissions/0b80d212-c23d-496d-8c96-294d25f54f3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.UnimodQuot
theorem _root_.solution {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ ψ : L →ₗ[𝓞 K] 𝓞 K, ∀ x : ↥(L ⊓ rs (𝓞 K) S), ψ ⟨x, x.2.1⟩ = φ x := by
  let N : Submodule (𝓞 K) L := (rs (𝓞 K) S).comap L.subtype
  have hflat : Module.Flat (𝓞 K) (L ⧸ N) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro q ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    have h1 : N.mkQ ((a : 𝓞 K) • x) = 0 := by rw [map_smul]; exact ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h2 : (algebraMap (𝓞 K) K a) • (x : V) ∈ S := by
      rw [algebraMap_smul]; exact h1
    have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact (S.smul_mem_iff h3).1 h2
  have : Module.FinitePresentation (𝓞 K) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : L →ₗ[𝓞 K] V := L.subtype ∘ₗ (LinearMap.id - s ∘ₗ N.mkQ)
  have hρ : ∀ x, ρ x ∈ L ⊓ rs (𝓞 K) S := by
    intro x
    refine ⟨(x - s (N.mkQ x)).2, ?_⟩
    have : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      have := LinearMap.congr_fun hs (N.mkQ x)
      rw [LinearMap.comp_apply] at this
      rw [this, LinearMap.id_apply, sub_self]
    exact this
  refine ⟨φ ∘ₗ ρ.codRestrict _ hρ, fun x => ?_⟩
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  have h0 : N.mkQ ⟨x, x.2.1⟩ = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2.2
  show ((⟨x, x.2.1⟩ - s (N.mkQ ⟨x, x.2.1⟩) : L) : V) = x
  rw [h0, map_zero, sub_zero]
end GlobalTheory.UnimodQuot
