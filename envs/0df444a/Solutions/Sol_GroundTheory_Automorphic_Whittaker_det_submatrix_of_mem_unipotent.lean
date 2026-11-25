-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.det_submatrix_of_mem_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:45.069357+00:00
-- url     : https://prove2.me/submissions/069171ab-2ca0-470c-8aef-46bb5e465429

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {v : GL (Fin n) F} (hv : v ∈ Iwasawa.unipotent F n)
    {m : ℕ} {c : Fin m → Fin n} (hc : Function.Injective c) :
    ((v : Matrix (Fin n) (Fin n) F).submatrix c c).det = 1 := by
  classical
  have hbt : ((v : Matrix (Fin n) (Fin n) F).submatrix c c).BlockTriangular (id ∘ c) :=
    ((Iwasawa.mem_unipotent F n).1 hv).1.submatrix
  rw [hbt.det]
  refine Finset.prod_eq_one fun a ha => ?_
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
  have : Unique {y // (id ∘ c) y = (id ∘ c) x} :=
    ⟨⟨⟨x, rfl⟩⟩, fun y => Subtype.ext (hc y.2)⟩
  rw [det_unique, toSquareBlock_def, of_apply,
    ← Unique.eq_default (⟨x, rfl⟩ : {y // (id ∘ c) y = (id ∘ c) x})]
  simp only [submatrix_apply]
  exact ((Iwasawa.mem_unipotent F n).1 hv).2 (c x)
end GroundTheory.Automorphic.Whittaker
