-- Prove2me | solution 1 for GlobalTheory.HermDiag.exists_orthogonal_basis_cons_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:42.368693+00:00
-- url     : https://prove2.me/submissions/222240fa-4fd9-4b29-9191-3a721742a49b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) {x : V} (hx : B x x ≠ 0) {d : ℕ}
    (v' : Basis (Fin d) E (LinearMap.ker (B.flip x)))
    (hv' : ∀ i j, i ≠ j → B (v' i) (v' j) = 0) :
    ∃ v : Basis (Fin (d + 1)) E V, v 0 = x ∧ ∀ i j, i ≠ j → B (v i) (v j) = 0 := by
  let b : Basis (Fin (d + 1)) E V :=
    Basis.mkFinCons x v'
      (by
        intro t y hy hc
        have hy' : B y x = 0 := by simpa using hy
        have h3 : B (t • x + y) x = 0 := by rw [hc]; simp
        rw [LinearMap.map_add, LinearMap.add_apply, hy', add_zero, LinearMap.map_smul,
          LinearMap.smul_apply, smul_eq_mul] at h3
        exact (mul_eq_zero.1 h3).resolve_right hx)
      (by
        intro y
        refine ⟨-B y x / B x x, ?_⟩
        simp [div_mul_cancel₀ _ hx])
  have hk : ∀ i, B (v' i) x = 0 := fun i => (v' i).prop
  refine ⟨b, by simp [b], ?_⟩
  simp only [b, Basis.coe_mkFinCons]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [← hB, hk, map_zero]
  · exact hk i
  · exact hv' i j (ne_of_apply_ne _ hij)
end GlobalTheory.HermDiag
