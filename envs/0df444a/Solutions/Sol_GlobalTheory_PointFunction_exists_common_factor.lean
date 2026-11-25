-- Prove2me | solution 1 for GlobalTheory.PointFunction.exists_common_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:50.937232+00:00
-- url     : https://prove2.me/submissions/5caf0785-7547-474b-ba90-b65855f6b9af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NonemptyAlgHomAlgebraicClosure
import Theorems.Thm_GlobalTheory_PointFunction_nonempty_algHom_algebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PointFunction
open IsLocalRing
namespace GlobalTheory.PointFunction
theorem _root_.solution (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (q : Ideal A) [q.IsPrime] (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k)
    (hφ : ∀ a, φ a = 0 ↔ a ∈ q) :
    ∃ χ : AlgebraicClosure q.ResidueField →ₐ[K] k,
      χ.comp (IsScalarTower.toAlgHom K A (AlgebraicClosure q.ResidueField)) = φ := by
  letI : Algebra A k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A k := .of_algebraMap_eq fun x => (φ.commutes x).symm
  let g : q.ResidueField →ₐ[A] k := Ideal.ResidueField.liftₐ q (Algebra.ofId A k)
    (fun a ha => (hφ a).2 ha) (fun a ha => by
      have : φ a ≠ 0 := fun h => ha ((hφ a).1 h)
      exact isUnit_iff_ne_zero.2 this)
  letI : Algebra q.ResidueField k := g.toRingHom.toAlgebra
  haveI : IsScalarTower A q.ResidueField k := .of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨χ⟩ := nonempty_algHom_algebraicClosure q.ResidueField k
  refine ⟨(χ.restrictScalars A).restrictScalars K, ?_⟩
  ext a
  exact (χ.restrictScalars A).commutes a
end GlobalTheory.PointFunction
