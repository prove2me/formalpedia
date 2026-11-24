-- Prove2me | solution 1 for GlobalTheory.SW.Model.mem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:36.414241+00:00
-- url     : https://prove2.me/submissions/59a6abb2-8c8d-4d82-a664-969cf27685e2

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
omit [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution {m : ℕ} (Λ : Lt E m) {s R : ℕ} (h : s.Coprime R) {v : Fin m → E}
    (h1 : (s : E) • v ∈ Λ) (h2 : (R : E) • v ∈ Λ) : v ∈ Λ := by
  have hc : IsCoprime (s : ℤ) (R : ℤ) := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨a, b, hab⟩ := hc
  have e : v = a • ((s : E) • v) + b • ((R : E) • v) := by
    rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, ← add_smul]
    have : (a : E) * s + b * R = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → E) hab
    rw [this, one_smul]
  rw [e]
  exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h1 a) (Λ.toAddSubgroup.zsmul_mem h2 b)
end GlobalTheory.SW.Model
