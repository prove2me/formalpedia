-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_orthogonal_basis_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:01:31.590586+00:00
-- url     : https://prove2.me/submissions/703a18f0-ad53-4427-a417-864903ffc08f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_exists_apply_self_ne_zero
import Theorems.Thm_GlobalTheory_HermDiag_finrank_ker_flip_add_one
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_cons_of_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E}
namespace GlobalTheory.HermDiag
universe u in
theorem _root_.solution (h2 : (2 : E) ≠ 0) (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (B : V →ₗ[E] V →ₛₗ[c] E), (∀ x y, c (B x y) = B y x) → finrank E V = d →
      ∃ v : Basis (Fin d) E V, ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  induction d with
  | zero =>
    intro V _ _ _ B _ hd
    exact ⟨basisOfFinrankZero hd, fun i => i.elim0⟩
  | succ d ih =>
    intro V _ _ _ B hB hd
    obtain rfl | hne := eq_or_ne B 0
    · exact ⟨Module.finBasisOfFinrankEq E V hd, fun _ _ _ => rfl⟩
    obtain ⟨x, hx⟩ := exists_apply_self_ne_zero h2 hB hne
    have hk := finrank_ker_flip_add_one hx
    obtain ⟨v', hv'⟩ := ih
      (B.domRestrict₁₂ (LinearMap.ker (B.flip x)) (LinearMap.ker (B.flip x)))
      (fun y z => hB y z) (by omega)
    obtain ⟨v, -, hv⟩ := exists_orthogonal_basis_cons_of_ker hB hx v' hv'
    exact ⟨v, hv⟩
end GlobalTheory.HermDiag
