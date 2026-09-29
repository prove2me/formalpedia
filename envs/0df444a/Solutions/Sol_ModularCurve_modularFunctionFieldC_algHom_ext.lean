-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldC_algHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/72631756-8a22-586c-9216-363cd8e3694a

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] {A : Type*} [Semiring A] [Algebra K A]
    {f g : modularFunctionFieldC K ℓ →ₐ[K] A}
    (h1 : f ⟨jqModC K, jqModC_mem K ℓ⟩ = g ⟨jqModC K, jqModC_mem K ℓ⟩)
    (h2 : f ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = g ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := modularFunctionFieldC K ℓ)
    (s := ({jqModC K, jqNModC K ℓ} : Set (LaurentSeries K))) rfl (fun x hx => ?_)
  rcases hx with rfl | hx
  · exact h1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h2

#print axioms solution

end S_ModularCurve_modularFunctionFieldC_algHom_ext
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext (solution)
