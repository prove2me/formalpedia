-- Prove2me | solution 1 for GlobalTheory.MaxLatStruct.colon_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:30.669285+00:00
-- url     : https://prove2.me/submissions/7357ac84-1a31-4b4a-9365-04e1c0375aa5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_basis
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice_denom


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
omit [StarRing K]
namespace GlobalTheory.MaxLatStruct
theorem _root_.solution [FiniteDimensional K V] {N : Submodule R V} (hN : N.FG)
    (hsp : Submodule.span K (M : Set V) = ⊤) : M.colon (N : Set V) ≠ ⊥ := by
  obtain ⟨s, _, b, hbv, hsL⟩ := dualLattice_basis (R := R) M hsp
  obtain ⟨d, hd0, hd⟩ := dualLattice_denom (R := R) b N hN
  have hle : Submodule.span R (Set.range b) ≤ M := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; rw [hbv]; exact hsL i.2
  intro e
  have : d ∈ M.colon (N : Set V) := Submodule.mem_colon.2 fun y hy => hle (hd y hy)
  rw [e] at this
  exact hd0 this
end GlobalTheory.MaxLatStruct
