-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:14:05.556262+00:00
-- url     : https://prove2.me/submissions/9982c391-88a2-4483-982c-2fa334150343

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (hA : UniP A M) (hB : UniP B M) : UniP (A × B) M := by
  obtain ⟨ΩA, cA, pA⟩ := hA
  obtain ⟨ΩB, cB, pB⟩ := hB
  let f : (Fin M → A) × (Fin M → B) → (Fin M → A × B) := fun p i => (p.1 i, p.2 i)
  have hf : Continuous f := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  refine ⟨f '' (ΩA ×ˢ ΩB), (cA.prod cB).image hf, ?_⟩
  rintro y ⟨z, hz⟩
  have h1 : (fun i => (z i).1) ⬝ᵥ (fun i => (y i).1) = 1 := by
    have := congrArg Prod.fst hz
    simpa [dotProduct, Prod.fst_sum] using this
  have h2 : (fun i => (z i).2) ⬝ᵥ (fun i => (y i).2) = 1 := by
    have := congrArg Prod.snd hz
    simpa [dotProduct, Prod.snd_sum] using this
  obtain ⟨a, za, m1, m2, m3⟩ := pA _ ⟨_, h1⟩
  obtain ⟨b, zb, n1, n2, n3⟩ := pB _ ⟨_, h2⟩
  have hab : ((MulEquiv.prodUnits.symm (a, b) : (A × B)ˣ) : A × B) = ((a : A), (b : B)) := rfl
  refine ⟨MulEquiv.prodUnits.symm (a, b), fun i => (za i, zb i),
    ⟨(_, _), ⟨m1, n1⟩, ?_⟩, ⟨(za, zb), ⟨m2, n2⟩, rfl⟩, ?_⟩
  · ext i <;> simp [f, hab]
  · refine Prod.ext ?_ ?_
    · simpa [dotProduct, Prod.fst_sum, hab] using m3
    · simpa [dotProduct, Prod.snd_sum, hab] using n3
end GlobalTheory.CompanionTheory.SW.PrimV
