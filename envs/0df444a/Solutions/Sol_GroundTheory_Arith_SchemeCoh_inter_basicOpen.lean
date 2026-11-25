-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.inter_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:13.982902+00:00
-- url     : https://prove2.me/submissions/a915bcbd-68ce-4a92-89dd-ea9b1ebe1e0e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {V : X.Opens} {κ : Type u} (h : κ → Γ(X, V)) :
    ∀ {n : ℕ} (i : Fin (n + 1) → κ),
      inter (X := X.toTopCat) (fun a => X.basicOpen (h a)) i = X.basicOpen (∏ a, h (i a))
  | 0, i => by
    rw [Fin.prod_univ_one]
    apply le_antisymm (inter_le _ i 0)
    intro x hx
    rw [mem_inter_iff]
    intro a
    rwa [Fin.fin_one_eq_zero a]
  | n + 1, i => by
    rw [inter_succ, solution h (i ∘ Fin.succ), Fin.prod_univ_succ (fun a => h (i a)),
      Scheme.basicOpen_mul]
    rfl
end GroundTheory.Arith.SchemeCoh
