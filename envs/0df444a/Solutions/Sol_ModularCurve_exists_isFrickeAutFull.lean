-- Prove2me | solution 1 for ModularCurve.exists_isFrickeAutFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9354c7a4-b2b7-59df-a528-3890efdc9285

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_isFrickeAut
import Theorems.Thm_ModularCurve_full_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isFrickeAutFull
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_isFrickeAutFull.ModularCurve AlgebraicCurve IntermediateField"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsFrickeAutFull qExpand qExpand_one_apply jq jqN modularFunctionField modularFunctionFieldFull exists_isFrickeAut full_eq_of_prime"
p2m_open "ModularCurve"

namespace W2B

theorem cast_algEquiv_exists {E E' : IntermediateField ℚ (LaurentSeries ℚ)} (h : E = E') (σ : E ≃ₐ[ℚ] E) :
    ∃ σ' : E' ≃ₐ[ℚ] E', ∀ x : E', ((σ' x : E') : LaurentSeries ℚ) = σ ⟨x, h ▸ x.2⟩ := by
  subst h
  exact ⟨σ, fun _ => rfl⟩

end W2B

end ModularCurve

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ, IsFrickeAutFull ℓ σ := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hfull : modularFunctionFieldFull ℓ = modularFunctionField ℓ := ModularCurve.full_eq_of_prime hℓ.out
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isFrickeAut ℓ
  obtain ⟨σ', hσ'⟩ := ModularCurve.W2B.cast_algEquiv_exists hfull.symm σ
  refine ⟨σ', ?_⟩
  intro a b hab _ _
  have hcases : a = 1 ∧ ℓ = b ∨ ℓ = a ∧ b = 1 := by
    have hprime : (a * b).Prime := hab ▸ hℓ.out
    rcases Nat.prime_mul_iff.mp hprime with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · right; exact ⟨hab.symm.trans (mul_one a), rfl⟩
    · left; exact ⟨rfl, hab.symm.trans (one_mul b)⟩

  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jq →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ jq := by
      rintro y hy rfl
      exact congrArg Subtype.val hσ.1
    apply Subtype.ext
    rw [hσ']
    exact H _ _ (qExpand_one_apply jq)
  · have H : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionField ℓ), y = jqN ℓ →
        ((σ ⟨y, hy⟩ : modularFunctionField ℓ) : LaurentSeries ℚ) = qExpand ℚ 1 jq := by
      rintro y hy rfl
      exact (congrArg Subtype.val hσ.2).trans (qExpand_one_apply jq).symm
    apply Subtype.ext
    rw [hσ']
    exact H _ _ rfl

end

end S_ModularCurve_exists_isFrickeAutFull
end P2MW
export P2MW.S_ModularCurve_exists_isFrickeAutFull (solution)
