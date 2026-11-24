-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.int_of_eT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:16.899117+00:00
-- url     : https://prove2.me/submissions/e982ef4f-965a-455d-b23d-2ce1a8c2809b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
omit [IsCMField E]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {q : ℕ} (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ 2 * NumberField.discr E) {w : E}
    (h1 : IsIntegral ℤ ((q : E) * w)) (h2 : ∀ c : 𝓞 E, eT ((c : E) * w) = 1) : IsIntegral ℤ w := by
  have h3 : IsIntegral ℤ ((NumberField.discr E : E) * w) := by
    have hw : w ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
      intro a ha
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨k, hk⟩ := (eT_eq_one_iff _).1 (h2 c)
      exact ⟨k, by rw [Algebra.traceForm_apply, mul_comm]; exact hk.symm⟩
    have h4 := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰
      (NumberField.discr_mem_differentIdeal E (𝓞 E))
    rw [coeIdeal_differentIdeal ℤ ℚ] at h4
    have h5 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))).1 h4 w hw
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h5
    have hb : (b : E) = (NumberField.discr E : E) * w := by simpa using hb
    rw [← hb]; exact b.2
  have h6 : IsCoprime (q : ℤ) (NumberField.discr E) :=
    ((Nat.prime_iff_prime_int.1 hq).irreducible.coprime_iff_not_dvd).2 fun h => hd (h.mul_left 2)
  obtain ⟨a, b, hab⟩ := h6
  have h7 : (a : E) * q + b * (NumberField.discr E : E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → E) hab
  have : w = a • ((q : E) * w) + b • ((NumberField.discr E : E) * w) := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-w) * h7
  rw [this]
  exact (h1.smul a).add (h3.smul b)
end GlobalTheory.SW.HeckeId
