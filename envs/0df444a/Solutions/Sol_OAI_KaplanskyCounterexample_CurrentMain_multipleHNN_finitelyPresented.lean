-- Prove2me | solution 1 for OAI.KaplanskyCounterexample.CurrentMain.multipleHNN_finitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:40:28.574993+00:00
-- url     : https://prove2.me/submissions/d4bda4c7-ab08-48c7-9b91-26698ede3d9f

import Mathlib
import Definitions.Def_OAIQWKAP000

section
-- module Solutions.OAIQW_Kaplansky.FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite presentations of finite-relation quotients and products. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma conGen_ker_finite {G J : Type*} [Group G] [Finite J] (u v : J → G) :
    (conGen (fun x y => ∃ j, x=u j ∧ y=v j)).mk'.ker.IsFinitelyNormallyGenerated := by
  let c := conGen (fun x y => ∃ j, x=u j ∧ y=v j)
  let R := Set.range (fun j => u j * (v j)⁻¹)
  refine ⟨R, Set.finite_range _, ?_⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    have he : c.mk' (u j) = c.mk' (v j) :=
      (Con.eq c).mpr (ConGen.Rel.of _ _ ⟨j, rfl, rfl⟩)
    change c.mk' (u j * (v j)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  · let q := QuotientGroup.mk' (Subgroup.normalClosure R)
    have hc : c ≤ Con.ker q := by
      apply Con.conGen_le.mpr
      rintro _ _ ⟨j, rfl, rfl⟩
      apply (Con.ker_rel q).mpr
      apply mul_inv_eq_one.mp
      rw [← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    intro w hw
    apply (QuotientGroup.eq_one_iff w).mp
    change q w = 1
    rw [← map_one q]
    apply hc
    exact (Con.eq c).mp (MonoidHom.mem_ker.mp hw |>.trans (map_one c.mk').symm)

lemma finitelyPresented_finite_relations {G J : Type*} [Group G]
    [Group.IsFinitelyPresented G] [Finite J] (u v : J → G) :
    Group.IsFinitelyPresented (conGen (fun x y => ∃ j, x=u j ∧ y=v j)).Quotient :=
  Group.IsFinitelyPresented.of_surjective _ Con.mk'_surjective (conGen_ker_finite u v)

end KaplanskyCounterexample.CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_Kaplansky.HNNPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite presentation of multiple HNN extensions and character twists. -/

noncomputable section

open scoped Classical

namespace KaplanskyCounterexample.CurrentMain

lemma multipleHNN_finitelyPresented_oai {H I : Type*} [Group H]
    [Group.IsFinitelyPresented H] [Finite I]
    (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i) [∀ i, Finite (A i)] :
    Group.IsFinitelyPresented (MultipleHNN.Extension A B φ) := by
  let u : (Σ i, A i) → Monoid.Coprod H (FreeGroup I) := fun j =>
    Monoid.Coprod.inr (FreeGroup.of j.1) * Monoid.Coprod.inl j.2.val
  let v : (Σ i, A i) → Monoid.Coprod H (FreeGroup I) := fun j =>
    Monoid.Coprod.inl (φ j.1 j.2).val * Monoid.Coprod.inr (FreeGroup.of j.1)
  have hc : MultipleHNN.con A B φ = conGen (fun x y => ∃ j, x=u j ∧ y=v j) := by
    unfold MultipleHNN.con
    congr 1
    funext x y
    apply propext
    constructor
    · rintro ⟨i, a, hx, hy⟩
      exact ⟨⟨i,a⟩,hx,hy⟩
    · rintro ⟨⟨i,a⟩,hx,hy⟩
      exact ⟨i,a,hx,hy⟩
  change @Group.IsFinitelyPresented (MultipleHNN.con A B φ).Quotient
    (Con.group (MultipleHNN.con A B φ))
  rw [hc]
  exact finitelyPresented_finite_relations u v

end KaplanskyCounterexample.CurrentMain

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KaplanskyCounterexample.CurrentMain.multipleHNN_finitelyPresented_oai.{u_1, u_2} := @OAI.KaplanskyCounterexample.CurrentMain.multipleHNN_finitelyPresented_oai.{u_1, u_2}
