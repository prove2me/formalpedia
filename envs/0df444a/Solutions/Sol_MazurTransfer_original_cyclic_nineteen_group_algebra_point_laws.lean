-- Prove2me | solution 1 for MazurTransfer.original_cyclic_nineteen_group_algebra_point_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T21:52:49.755922+00:00
-- url     : https://prove2.me/submissions/388e4b59-01e3-407f-973c-1c712cac257c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original cyclic nineteen group algebra represents literal nineteenth roots over every commutative coefficient algebra, retaining the same multiplication and all coefficient maps.
Named downstream consumer: normalization of the same selected integral pi quotient and pushforward of its norm Kummer classes.
-/
import Definitions.Def_MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
noncomputable section
open MazurTransfer.CyclicNineteenGroupAlgebraPoints
namespace MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointBoundary20261020
end MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the group algebra of Z/19 represents LITERAL mu19 over
EVERY coefficient algebra; retain multiplication and every coefficient map.
Named downstream consumer: normalization of the SAME selected integral
pi quotient and pushforward of its actual norm Kummer classes.
-/

noncomputable section
namespace MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020
open scoped TensorProduct



theorem generator_pow_nineteen : generator ^ 19 = 1 := by
  apply Multiplicative.toAdd.injective
  change 19 • (1 : ZMod 19) = 0
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_self 19)

theorem generator_pow_val (m : Cyclic) : generator ^ m.toAdd.val = m := by
  apply Multiplicative.toAdd.injective
  change m.toAdd.val • (1 : ZMod 19) = m.toAdd
  simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val m.toAdd

theorem character_ext {T : Type} [Monoid T] {f g : Cyclic →* T}
    (h : f generator = g generator) : f = g := by
  apply MonoidHom.ext
  intro m
  rw [← generator_pow_val m, map_pow, map_pow, h]

variable {T : Type} [CommRing T]

theorem root_nsmul (ζ : rootsOfUnity 19 T) : (19 : ℕ) • Additive.ofMul ζ.val = 0 := by
  change Additive.ofMul (ζ.val ^ 19) = Additive.ofMul (1 : Tˣ)
  exact congrArg Additive.ofMul ((mem_rootsOfUnity 19 ζ.val).mp ζ.property)





theorem rootCharacter_generator (ζ : rootsOfUnity 19 T) : rootCharacter ζ generator = ζ.val := by
  have h := ZMod.lift_coe 19 (rootLiftData ζ) 1
  have h' : (ZMod.lift 19 (rootLiftData ζ)) (1 : ZMod 19) = Additive.ofMul ζ.val := by
    simpa [rootLiftData] using h
  exact congrArg Additive.toMul h'

variable (R : Type) [CommRing R] [Algebra R T]





theorem rootOfPoint_val (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    ((rootOfPoint R f : Tˣ) : T) = f (MonoidAlgebra.single generator 1) := rfl



theorem rootOfPoint_pointOfRoot (ζ : rootsOfUnity 19 T) : rootOfPoint R (pointOfRoot R ζ) = ζ := by
  apply Subtype.ext
  apply Units.ext
  rw [rootOfPoint_val]
  change MonoidAlgebra.lift R T Cyclic _ (MonoidAlgebra.single generator 1) = _
  rw [MonoidAlgebra.lift_single, one_smul]
  exact congrArg (fun u : Tˣ => (u : T)) (rootCharacter_generator ζ)

theorem pointOfRoot_rootOfPoint (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    pointOfRoot R (rootOfPoint R f) = f := by
  apply WithConv.ext
  apply (MonoidAlgebra.lift R T Cyclic).symm.injective
  apply character_ext
  rw [pointOfRoot, WithConv.ofConv_toConv, Equiv.symm_apply_apply]
  change ((rootCharacter (rootOfPoint R f) generator : Tˣ) : T) = _
  rw [rootCharacter_generator]
  rfl





theorem rootOfPoint_mul (f g : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    rootOfPoint R (f * g) = rootOfPoint R f * rootOfPoint R g := by
  apply Subtype.ext
  apply Units.ext
  change (f * g).ofConv (MonoidAlgebra.single generator 1) =
    f.ofConv (MonoidAlgebra.single generator 1) * g.ofConv (MonoidAlgebra.single generator 1)
  have hc : Coalgebra.comul (R := R) (MonoidAlgebra.single generator (1 : R)) =
      MonoidAlgebra.single generator 1 ⊗ₜ[R] MonoidAlgebra.single generator 1 := by
    simp [MonoidAlgebra.comul_single]
  rw [AlgHom.convMul_apply, hc, Algebra.TensorProduct.lift_tmul]

theorem rootOfPoint_one : rootOfPoint R (1 : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change algebraMap R T (Coalgebra.counit (R := R) (MonoidAlgebra.single generator (1 : R))) = 1
  simp [MonoidAlgebra.counit_single]

theorem rootOfPoint_natural {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    rootOfPoint R (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (rootOfPoint R f) := by
  apply Subtype.ext
  apply Units.ext
  rfl

theorem cyclic_pow_nineteen (m : Cyclic) : m ^ 19 = 1 := by
  rw [← generator_pow_val m, ← pow_mul, Nat.mul_comm, pow_mul, generator_pow_nineteen, one_pow]



theorem pointRootsCharacter_generator (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    pointRootsCharacter R f generator = rootOfPoint R f := rfl



end MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020


theorem solution : (Eq (instHPow.hPow MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator 19) 1) ∧ (∀ (m : MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic),
  Eq
    (instHPow.hPow MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator
      (EquivLike.toFunLike.coe Multiplicative.toAdd m).val)
    m) ∧ (∀ {T : Type} [inst : Monoid T] {f g : MonoidHom MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic T},
  Eq (MonoidHom.instFunLike.coe f MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
      (MonoidHom.instFunLike.coe g MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator) →
    Eq f g) ∧ (∀ {T : Type} [inst : CommRing T] (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq (instHSMul.hSMul 19 (EquivLike.toFunLike.coe Additive.ofMul ζ.val)) 0) ∧ (∀ {T : Type} [inst : CommRing T] (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq
    (MonoidHom.instFunLike.coe (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootCharacter ζ)
      MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
    ζ.val) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f).val.val
    (AlgHom.funLike.coe f.ofConv (MonoidAlgebra.single MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator 1))) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (ζ : Subtype fun x => SetLike.instMembership.mem (rootsOfUnity 19 T) x),
  Eq
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointOfRoot R ζ))
    ζ) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointOfRoot R
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f))
    f) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f g : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R (instHMul.hMul f g))
    (instHMul.hMul (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f)
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R g))) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T],
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R (1 : WithConv (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic →ₐ[R] T))) 1) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T] {T' : Type}
  [inst_3 : CommRing T'] [inst_4 : Algebra R T'] (a : AlgHom R T T')
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R { ofConv := a.comp f.ofConv })
    (MonoidHom.instFunLike.coe (restrictRootsOfUnity a.toRingHom 19)
      (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f))) ∧ (∀ (m : MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic), Eq (instHPow.hPow m 19) 1) ∧ (∀ {T : Type} [inst : CommRing T] (R : Type) [inst_1 : CommRing R] [inst_2 : Algebra R T]
  (f : WithConv (AlgHom R (MonoidAlgebra R MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic) T)),
  Eq
    (MonoidHom.instFunLike.coe (MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointRootsCharacter R f)
      MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator)
    (MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint R f)) := by
  exact ⟨MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.generator_pow_nineteen, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.generator_pow_val, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.character_ext, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.root_nsmul, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootCharacter_generator, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootOfPoint_val, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootOfPoint_pointOfRoot, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.pointOfRoot_rootOfPoint, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootOfPoint_mul, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootOfPoint_one, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.rootOfPoint_natural, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.cyclic_pow_nineteen, MazurTransfer.OriginalCyclicNineteenGroupAlgebraPointProof20261020.pointRootsCharacter_generator⟩
#print axioms solution
