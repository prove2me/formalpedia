-- Prove2me | solution 1 for GlobalTheory.WeilCont.isContOn_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:38.401806+00:00
-- url     : https://prove2.me/submissions/82f3bc8e-d016-441f-b996-24728683d132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsContOnOfLocal
import Theorems.Thm_GlobalTheory_WeilCont_pureA_adeleJoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
open GlobalTheory GlobalTheory.WeilCont
variable (F : Type) [Field F] [NumberField F] {κ : Type}
namespace GlobalTheory.WeilCont
theorem _root_.solution [Fintype κ] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] {G : Type} [Group G] [TopologicalSpace G]
    {om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)}
    (hfin : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ p0 : G, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (hsl : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → FiniteAdeleRing (𝓞 F) F,
      ∃ s : G → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Continuous s ∧ ∀ p x, s p x = om p Φ (adeleJoin F x y)) :
    GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass F) om := by
  intro l hl φ hφ
  change φ ∈ GlobalTheory.WeilM.schA F κ at hφ
  change ∀ g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F),
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, l (GlobalTheory.WeilM.pureA F f g) = T f at hl
  rw [continuous_iff_continuousAt]
  intro p0
  obtain ⟨N, hN, m, g, y, hgSB, hgy, hrep⟩ := hfin φ hφ p0
  choose T hT using fun i => hl (g i) (hgSB i)
  choose s hs hsx using fun j => hsl φ hφ (y j)
  have hcont : Continuous fun p => ∑ i, T i (s i p) :=
    continuous_finsetSum _ (fun i _ => (T i).continuous.comp (hs i))
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with p hp
  obtain ⟨f, hf⟩ := hrep p hp
  have hfs : ∀ j, f j = s j p := by
    intro j
    ext x
    rw [hsx, hf, Finset.sum_apply, Finset.sum_eq_single j]
    · rw [pureA_adeleJoin, hgy j j, if_pos rfl, mul_one]
    · intro i _ hij
      rw [pureA_adeleJoin, hgy i j, if_neg hij, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [hf, map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [hT, hfs])
end GlobalTheory.WeilCont
