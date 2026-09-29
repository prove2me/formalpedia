-- Prove2me | solution 1 for ModularCurve.IgusaScheme.iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b3831457-43b9-56fb-a2b6-d6db5240a601

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf chartFinOpen chartInfOpen"
p2m_open "ModularCurve.IgusaScheme ModularCurve"

section ChartIntersection

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

theorem ιFin_apply_eq_ιInf_apply_iff (a : ↥(XFin N ℓ)) (b : ↥(XInf N ℓ)) :
    (ιFin N ℓ).base a = (ιInf N ℓ).base b ↔ ∃ m : ↥(XMid N ℓ), (fFin N ℓ).base m = a ∧ (fInf N ℓ).base m = b := by
  have h := Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin N ℓ) (fInf N ℓ))
    (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := a) (xj := b)
  have h' : (ιFin N ℓ).base a = (ιInf N ℓ).base b ↔
      ∃ (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
        (x : ↥((span (fFin N ℓ) (fInf N ℓ)).obj k)),
        ((span (fFin N ℓ) (fInf N ℓ)).map fi).base x = a ∧ ((span (fFin N ℓ) (fInf N ℓ)).map fj).base x = b := h
  rw [h']
  constructor
  · rintro ⟨k, fi, fj, x, ha, hb⟩
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      obtain rfl : fj = WidePushoutShape.Hom.init _ := Subsingleton.elim _ _
      exact ⟨x, ha, hb⟩
    · change WidePushoutShape.Hom _ _ at fj; cases fj
    · change WidePushoutShape.Hom _ _ at fi; cases fi
  · rintro ⟨m, ha, hb⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, m, ha, hb⟩

theorem ιInf_apply_mem_range_ιFin_iff (b : ↥(XInf N ℓ)) :
    (ιInf N ℓ).base b ∈ Set.range (ιFin N ℓ).base ↔ b ∈ Set.range (fInf N ℓ).base := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, -, hm⟩ := (ιFin_apply_eq_ιInf_apply_iff N ℓ a b).mp ha
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fFin N ℓ).base m, (ιFin_apply_eq_ιInf_apply_iff N ℓ _ _).mpr ⟨m, rfl, rfl⟩⟩

theorem ιFin_apply_mem_range_ιInf_iff (a : ↥(XFin N ℓ)) :
    (ιFin N ℓ).base a ∈ Set.range (ιInf N ℓ).base ↔ a ∈ Set.range (fFin N ℓ).base := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨m, hm, -⟩ := (ιFin_apply_eq_ιInf_apply_iff N ℓ a b).mp hb.symm
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(fInf N ℓ).base m, ((ιFin_apply_eq_ιInf_apply_iff N ℓ _ _).mpr ⟨m, rfl, rfl⟩).symm⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fInf :
    Set.range (fInf N ℓ).base = (PrimeSpectrum.basicOpen (jInvChartInf N ℓ) : Set (PrimeSpectrum ↥(chartAlgInf N ℓ))) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jInvChartInf N ℓ)

set_option synthInstance.maxHeartbeats 1600000 in

theorem range_fFin :
    Set.range (fFin N ℓ).base = (PrimeSpectrum.basicOpen (jChartFin N ℓ) : Set (PrimeSpectrum ↥(chartAlgFin N ℓ))) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jChartFin N ℓ)

end ChartIntersection

end ModularCurve.IgusaScheme

open _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen.ModularCurve.IgusaScheme in
theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ιInf N ℓ ⁻¹ᵁ chartFinOpen N ℓ = PrimeSpectrum.basicOpen (jInvChartInf N ℓ) ∧
    ιFin N ℓ ⁻¹ᵁ chartInfOpen N ℓ = PrimeSpectrum.basicOpen (jChartFin N ℓ) := by
  constructor
  · apply TopologicalSpace.Opens.ext
    ext b
    change (ιInf N ℓ).base b ∈ Set.range (ιFin N ℓ).base ↔ b ∈ (PrimeSpectrum.basicOpen (jInvChartInf N ℓ) : Set (PrimeSpectrum ↥(chartAlgInf N ℓ)))
    rw [ιInf_apply_mem_range_ιFin_iff, range_fInf]
    exact Iff.rfl
  · apply TopologicalSpace.Opens.ext
    ext a
    change (ιFin N ℓ).base a ∈ Set.range (ιInf N ℓ).base ↔ a ∈ (PrimeSpectrum.basicOpen (jChartFin N ℓ) : Set (PrimeSpectrum ↥(chartAlgFin N ℓ)))
    rw [ιFin_apply_mem_range_ιInf_iff, range_fFin]
    exact Iff.rfl

end S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (solution)
