-- Prove2me | solution 1 for GlobalTheory.DegCnt.GlueZ.mem_lattice_zeroTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:30.656924+00:00
-- url     : https://prove2.me/submissions/71e9e447-44a5-4e14-895e-c79058021894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardInnerLatticesWithDefiniteTraceLeNorm
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.GlueZ
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}
namespace GlobalTheory.DegCnt.GlueZ
theorem _root_.solution {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]
end GlobalTheory.DegCnt.GlueZ
