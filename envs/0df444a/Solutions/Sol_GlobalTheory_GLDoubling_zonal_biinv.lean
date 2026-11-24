-- Prove2me | solution 1 for GlobalTheory.GLDoubling.zonal_biinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:18.585379+00:00
-- url     : https://prove2.me/submissions/a0075ab1-8410-4027-aa92-42005b53b0da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {K : Subgroup G} {ω : G → ℂ} (h : IsZonal π K ω) (g : G) {x y : G} (hx : x ∈ K) (hy : y ∈ K) :
    ω (x * g * y) = ω g := by
  obtain ⟨v, hv, l, hl, -, e⟩ := h
  have h1 : π y v = v := by simpa using hv ⟨y, hy⟩
  have h2 : π.dual x⁻¹ l = l := by simpa using hl ⟨x⁻¹, inv_mem hx⟩
  rw [e, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1]
  conv_rhs => rw [← h2]
  simp [Module.Dual.transpose_apply]
end GlobalTheory.GLDoubling
