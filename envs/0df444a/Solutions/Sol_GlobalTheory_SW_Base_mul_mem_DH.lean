-- Prove2me | solution 1 for GlobalTheory.SW.Base.mul_mem_DH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:19.874801+00:00
-- url     : https://prove2.me/submissions/17269d7e-05af-4800-8a28-c9f1847a5fb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul

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
theorem _root_.solution {M : ℕ} {h g : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M)
    (hg : g ∈ DH E n M) : h * g ∈ DH E n M := by
  obtain ⟨hu, s, hs, hsM, y, hy, e⟩ := hh
  obtain ⟨gu, t, ht, htM, w, hw, f⟩ := hg
  refine ⟨?_, s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hsM htM,
    (M : E) • (y * w) + (t : E) • y + (s : E) • w, fun i j => ?_, ?_⟩
  · rw [ccT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ccT h), hu, one_mul, gu]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
      simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
    exact (((c M).mul (IsIntegral.sum _ fun k _ => (hy i k).mul (hw k j))).add
      ((c t).mul (hy i j))).add ((c s).mul (hw i j))
  · have : ((s * t : ℕ) : E) • (h * g - 1) = ((s : E) • (h - 1)) * ((t : E) • (g - 1)) +
        (t : E) • ((s : E) • (h - 1)) + (s : E) • ((t : E) • (g - 1)) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul, mul_comm (t : E) s,
        ← smul_add]
      congr 1
      noncomm_ring
    rw [this, e, f]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, mul_comm (M : E)]
end GlobalTheory.SW.Base
