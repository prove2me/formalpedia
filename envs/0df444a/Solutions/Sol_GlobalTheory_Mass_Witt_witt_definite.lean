-- Prove2me | solution 1 for GlobalTheory.Mass.Witt.witt_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:07.986371+00:00
-- url     : https://prove2.me/submissions/f9fdc030-4ced-4d16-aff3-3f8db30572d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Theorems.Thm_GlobalTheory_Mass_Witt_exists_isom_finset
import Theorems.Thm_GlobalTheory_Mass_Witt_isCompl_perp
import Theorems.Thm_GlobalTheory_Mass_Witt_perp_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Witt
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hpd
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨?_, fun U => ⟨isCompl_perp h ha U, ?_, ?_, perp_perp h hs ha U⟩⟩
  · intro U U' e he
    let bU := Module.finBasis K U
    obtain ⟨g, hg, hgb⟩ := exists_isom_finset h hs ha (fun i => (bU i : V))
      (fun i => (e (bU i) : V)) (fun i j => he _ _) Finset.univ
    refine ⟨g, hg, fun x => ?_⟩
    have hcomp : (g : V →ₗ[K] V).comp U.subtype = U'.subtype.comp (e : U →ₗ[K] U') := by
      apply bU.ext
      intro i
      simpa using hgb i (Finset.mem_univ i)
    exact LinearMap.congr_fun hcomp x
  · exact ⟨fun x y => hs.eq x y⟩
  · intro τ x hx
    show 0 < (τ (h x x)).re
    exact hpd τ x (fun h0 => hx (Subtype.ext h0))
end GlobalTheory.Mass.Witt
