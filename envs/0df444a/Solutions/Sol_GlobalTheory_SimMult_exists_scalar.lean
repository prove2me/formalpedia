-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:19.172162+00:00
-- url     : https://prove2.me/submissions/89f8b64d-c8eb-43e8-8d8c-9a372bf3efb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult
import Theorems.Thm_GlobalTheory_SimMult_exists_norm_mod
import Theorems.Thm_GlobalTheory_SimMult_mem_of_mul_eq_span
import Theorems.Thm_GlobalTheory_SimMult_exists_norm_level
import Theorems.Thm_GlobalTheory_SimMult_exists_bar_sub_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
namespace GlobalTheory.SimMult
theorem _root_.solution (l : Level H) (n : ℕ) (hn : 0 < n) (hM : l.M ∣ n) (hAn : l.A ∣ n) (ν : ℤ)
    (hν : IsCoprime ν (n : ℤ)) (hA : (l.A : ℤ) ∣ ν - 1) :
    ∃ c : 𝓞 E, (n : 𝓞 E) ∣ c * H.bar c - ν ∧ c - 1 ∈ l.Mb ∧ (l.A : 𝓞 E) ∣ c - 1 := by
  have hσ : ∀ x, (H.bar : 𝓞 E →+* 𝓞 E) ((H.bar : 𝓞 E →+* 𝓞 E) x) = x := HostModel.bar_bar H
  have hw : H.w0 + (H.bar : 𝓞 E →+* 𝓞 E) H.w0 = 1 := by
    change H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator]; ring
  obtain ⟨c, h1, h2, h3⟩ := exists_norm_level (H.bar : 𝓞 E →+* 𝓞 E) hσ hw ν
    (fun m hm h => exists_norm_mod _ hσ hw (exists_bar_sub_notMem H) m hm ν h)
    l.M l.A l.Mb l.prod l.coprime hA n hn hν
  have hMJ : (l.M : 𝓞 E) ∈ l.Mb :=
    mem_of_mul_eq_span l.prod
  refine ⟨c, h1, ?_, ?_⟩
  · refine (sup_le le_rfl ?_ : _ ≤ l.Mb) h2
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast hM) hMJ
  · rw [← Ideal.mem_span_singleton]
    refine (sup_le le_rfl ?_ : _ ≤ Ideal.span {(l.A : 𝓞 E)}) h3
    exact Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hAn)
end GlobalTheory.SimMult
