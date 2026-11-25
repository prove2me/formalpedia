-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:47.227715+00:00
-- url     : https://prove2.me/submissions/4fcfce47-c08b-4068-af8c-7c57defc1631

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan

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
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}
omit [IsDedekindDomain R]
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution (L : Submodule R V) (x : V)
    (hx : ∀ Q : Ideal R, Q.IsMaximal → ∃ s ∉ Q, s • x ∈ L) : x ∈ L := by
  by_contra hxL
  have hI : L.colon {x} ≠ ⊤ := by
    intro e
    have h1 : (1 : R) ∈ L.colon {x} := e ▸ Submodule.mem_top
    exact hxL (by simpa using Submodule.mem_colon.1 h1 x rfl)
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsx⟩ := hx p hp
  exact hs (hIp (Submodule.mem_colon.2 (by rintro _ rfl; exact hsx)))
end GlobalTheory.MaxLatStruct
