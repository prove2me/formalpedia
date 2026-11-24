-- Prove2me | solution 1 for GlobalTheory.Member.LatData.norm_entry_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:15.527747+00:00
-- url     : https://prove2.me/submissions/ec72db79-f069-412f-a1a3-5691f1257ae9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDataLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Member GlobalTheory.Member.LatData
open GlobalTheory.Up.Definite GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Member.LatData
theorem _root_.solution {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (hγ : IsUStab (1 : Matrix (Fin r) (Fin r) E) Λ γ) (φ : E →+* ℂ) (a b : Fin r) :
    ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
  have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
      fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
    ext a; simp
  have h1 := congrArg φ (hγ.1 (Pi.single b 1) (Pi.single b 1))
  rw [map_herm_one_self, map_herm_one_self, hcol] at h1
  have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single b] <;> simp +contextual
  have h3 := Complex.ofReal_injective h1
  rw [h2] at h3
  have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  rw [h3] at h4
  nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
end GlobalTheory.Member.LatData
