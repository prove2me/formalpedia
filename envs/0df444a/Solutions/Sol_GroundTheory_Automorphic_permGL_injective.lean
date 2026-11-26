-- Prove2me | solution 1 for GroundTheory.Automorphic.permGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:54:51.001984+00:00
-- url     : https://prove2.me/submissions/3d41058e-00c0-414c-815e-ba1338f79844

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
theorem _root_.solution : Function.Injective (permGL k : Equiv.Perm (Fin n) → GL (Fin n) k) := by
  first
    | (intro a b h
       have hm : (Matrix.permMatrixHom (n := Fin n) (R := k)) a = (Matrix.permMatrixHom (n := Fin n) (R := k)) b :=
         congrArg Units.val h
       have key : Function.Injective (fun σ : Equiv.Perm (Fin n) => (σ.permMatrix k)) := by
         intro s t hst
         refine Equiv.ext fun i => ?_
         have h1 := congrFun (congrFun hst i) (s i)
         simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq] at h1
         rw [if_pos trivial] at h1
         by_contra hne
         rw [if_neg (fun h2 => hne h2.symm)] at h1
         exact one_ne_zero h1
       have : a⁻¹ = b⁻¹ := key hm
       exact inv_injective this)

