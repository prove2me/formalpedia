-- Prove2me | solution 1 for GlobalTheory.Member.LatData.finite_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:00.946392+00:00
-- url     : https://prove2.me/submissions/654ad0b6-e1ef-42aa-9009-46dcde92385a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDataLattice
import Theorems.Thm_GlobalTheory_Member_LatData_norm_entry_le_one
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded


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
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    {γ : GL (Fin r) E | IsUStab (1 : Matrix (Fin r) (Fin r) E) Λ γ}.Finite := by
  obtain ⟨k, hk, hi⟩ := exists_common_den Λ hfg
  choose l hl hm using fun b : Fin r => exists_int_smul_mem Λ hsp (Pi.single b 1)
  have hfin := Set.Finite.pi' fun _ : Fin r => Set.Finite.pi' fun b : Fin r =>
    finite_bounded (data E r).Ψ (data E r).cmType (k * l b) (mul_ne_zero hk (hl b)) 1
  refine Set.Finite.of_finite_image
    (f := fun γ : GL (Fin r) E => fun a b => (γ : Matrix (Fin r) (Fin r) E) a b)
    (hfin.subset ?_) (fun x _ y _ h => Units.ext h)
  rintro _ ⟨γ, hγ, rfl⟩ a b
  refine ⟨?_, fun τ => norm_entry_le_one hγ τ.1 a b⟩
  have := hi _ ((hγ.2 _).1 (hm b)) a
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one] at this
  simpa [mul_assoc, Matrix.col] using this
end GlobalTheory.Member.LatData
