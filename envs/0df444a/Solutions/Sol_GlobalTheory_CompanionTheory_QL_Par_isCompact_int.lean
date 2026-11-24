-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.isCompact_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:25.611426+00:00
-- url     : https://prove2.me/submissions/2a105f38-7e5c-4fde-8406-fa17f9d174ec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isCompact_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Par
theorem _root_.solution (h : LF O ϖ nrm q) (n : ℕ) :
    IsCompact {m : Matrix (Fin n) (Fin n) F | IsInt O m} := by
  have e : {m : Matrix (Fin n) (Fin n) F | IsInt O m} =
      Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => (O : Set F))) := by
    ext m
    exact ⟨fun hm a _ b _ => hm a b, fun hm a b => hm a trivial b trivial⟩
  rw [e]
  exact isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => isCompact_O h))
end GlobalTheory.CompanionTheory.QL.Par
