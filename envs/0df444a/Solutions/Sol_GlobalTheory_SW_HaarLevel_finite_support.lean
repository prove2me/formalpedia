-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:35.779701+00:00
-- url     : https://prove2.me/submissions/2afb04e6-47e1-4d83-a7cc-ac0134214442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub
import Theorems.Thm_GlobalTheory_SW_HaarLevel_index_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) :
    (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  have hK : (R : K) ≠ 0 := by exact_mod_cast hR.ne'
  set f : Matrix κ ι (𝓞 K) →+ Matrix κ ι K ⧸ perSub K κ ι R :=
    (QuotientAddGroup.mk' (perSub K κ ι R)).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) (R : K)⁻¹).comp (incl K κ ι)) with hf
  have hfa : ∀ y, f y = (((R : K)⁻¹ • incl K κ ι y : Matrix κ ι K) :
    Matrix κ ι K ⧸ perSub K κ ι R) := fun _ => rfl
  have hker : (nsmulAddMonoidHom (R * R) : Matrix κ ι (𝓞 K) →+ _).range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, hfa, QuotientAddGroup.eq_zero_iff, mem_perSub]
    refine ⟨y, ?_⟩
    rw [nsmulAddMonoidHom_apply, map_nsmul, mul_smul, ← Nat.cast_smul_eq_nsmul K R (R • _),
      smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hcard : Nat.card f.range ≠ 0 := by
    rw [← AddSubgroup.index_ker]
    refine ne_zero_of_dvd_ne_zero ?_ (AddSubgroup.index_dvd_of_le hker)
    rw [index_nsmul]
    positivity
  have hfin : Finite f.range := Nat.finite_of_card_ne_zero hcard
  refine (Set.toFinite (f.range : Set (Matrix κ ι K ⧸ perSub K κ ι R))).subset fun q hq => ?_
  obtain ⟨y, hy⟩ := (intM_iff _).1 (h.1 _ hq)
  refine ⟨y, ?_⟩
  rw [hfa, hy, smul_smul, inv_mul_cancel₀ hK, one_smul, QuotientAddGroup.out_eq']
end GlobalTheory.SW.HaarLevel
