-- Prove2me | solution 1 for GlobalTheory.SW.Model.I_mem_Hn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:52.952915+00:00
-- url     : https://prove2.me/submissions/9f53d654-9fba-4768-9c07-fa29d86f8ffe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (N : ℕ) :
    (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (I • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 := by
    unfold imH
    rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]
    have : (2 * I)⁻¹ * (I - star I) = 1 := by
      have : star I = -I := conj_I
      rw [this]; field_simp; ring
    rw [this, one_smul]
  simpa [this] using Matrix.PosDef.one
end GlobalTheory.SW.Model
