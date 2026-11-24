-- Prove2me | solution 1 for GlobalTheory.JetSer.top_le_preimage_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.978798+00:00
-- url     : https://prove2.me/submissions/b44d73c1-ffc5-4eef-82ca-cbc759fc2bdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetSer
variable {A : Type} [CommRing A] {X : Scheme.{0}}
namespace GlobalTheory.JetSer
theorem _root_.solution {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  have hker : RingHom.ker q ≤ z.asIdeal := fun a ha => by
    obtain ⟨n, hn⟩ := hn a ha
    exact z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have := z.isPrime
  have hprime : (z.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let z₀ : ↥(Spec (CommRingCat.of B)) := (⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)
  have hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]
  have h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U := h trivial
  rw [← hz]
  simpa using h0
end GlobalTheory.JetSer
