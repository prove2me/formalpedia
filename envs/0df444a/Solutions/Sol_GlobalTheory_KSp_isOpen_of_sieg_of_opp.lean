-- Prove2me | solution 1 for GlobalTheory.KSp.isOpen_of_sieg_of_opp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:43:05.518284+00:00
-- url     : https://prove2.me/submissions/92e17b64-4f77-4e27-9192-778b87e06a80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
import Theorems.Thm_GlobalTheory_KSp_OpenCrit_nOf_mem
import Theorems.Thm_GlobalTheory_KSp_OpenCrit_pOf_mem
import Theorems.Thm_GlobalTheory_KSp_OpenCrit_eventually_isUnit
import Theorems.Thm_GlobalTheory_KSp_OpenCrit_tendsto_nOf
import Theorems.Thm_GlobalTheory_T_quadExt_topological_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp
open OpenCrit
namespace GlobalTheory.KSp
theorem _root_.solution (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))
end GlobalTheory.KSp
