-- Prove2me | solution 1 for GlobalTheory.SW.Base.cls_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:26.959828+00:00
-- url     : https://prove2.me/submissions/08b40b10-c29d-4a25-9c79-56052f46b13c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_mul_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_moves_one
import Theorems.Thm_GlobalTheory_SW_Base_moves_mul
import Theorems.Thm_GlobalTheory_SW_Base_moves_ccT

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
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution {M : ℕ} (Λ Λ' : Vset E n M) :
    (Quot.mk _ Λ : Cls E n M) = Quot.mk _ Λ' ↔ ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1 := by
  have : Equivalence fun Λ Λ' : Vset E n M => ∃ h ∈ DH E n M, Moves h Λ.1 Λ'.1 :=
    ⟨fun Λ => ⟨1, one_mem_DH M, moves_one _⟩,
      fun ⟨h, hh, m⟩ => ⟨ccT h, ccT_mem_DH hh, moves_ccT hh.1 m⟩,
      fun ⟨g, hg, m⟩ ⟨h, hh, m'⟩ => ⟨h * g, mul_mem_DH hh hg, moves_mul m m'⟩⟩
  exact Quot.eq.trans this.eqvGen_iff
end GlobalTheory.SW.Base
