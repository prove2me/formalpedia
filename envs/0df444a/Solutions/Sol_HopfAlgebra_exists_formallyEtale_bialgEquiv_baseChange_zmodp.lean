-- Prove2me | solution 1 for HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/49f4a05c-b909-5702-b574-dced906d0ed1

import Mathlib
import Theorems.Thm_Algebra_FormallyEtale_exists_baseChange_algEquiv_of_isReduced_zmodp
import Theorems.Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace HopfLift

section BC

variable {R : Type*} [CommRing R] {F : Type*} [CommRing F] [Algebra R F]
variable {X Y Z X' Y' : Type*} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
  [CommRing Z] [Algebra R Z] [CommRing X'] [Algebra R X'] [CommRing Y'] [Algebra R Y']
variable {Xb Yb Zb Xb' Yb' : Type*} [CommRing Xb] [Algebra F Xb] [CommRing Yb] [Algebra F Yb]
  [CommRing Zb] [Algebra F Zb] [CommRing Xb'] [Algebra F Xb'] [CommRing Yb'] [Algebra F Yb']

variable (F) in

private noncomputable abbrev bar (f : X →ₐ[R] Y) : F ⊗[R] X →ₐ[F] F ⊗[R] Y :=
  Algebra.TensorProduct.map (AlgHom.id F F) f

private theorem bar_tmul (f : X →ₐ[R] Y) (a : F) (x : X) : bar F f (a ⊗ₜ[R] x) = a ⊗ₜ[R] f x := rfl

private theorem bar_comp_apply (f : Y →ₐ[R] Z) (g : X →ₐ[R] Y) (z : F ⊗[R] X) :
    bar F (f.comp g) z = bar F f (bar F g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem bar_id_apply (z : F ⊗[R] X) : bar F (AlgHom.id R X) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (R F X Y) in

private noncomputable def κ : F ⊗[R] (X ⊗[R] Y) ≃ₐ[F] (F ⊗[R] X) ⊗[F] (F ⊗[R] Y) :=
  (Algebra.TensorProduct.assoc R R F F X Y).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R F F (F ⊗[R] X) Y).symm

private theorem κ_tmul (a : F) (x : X) (y : Y) :
    κ R F X Y (a ⊗ₜ[R] (x ⊗ₜ[R] y)) = (a ⊗ₜ[R] x) ⊗ₜ[F] ((1 : F) ⊗ₜ[R] y) := by
  simp [κ]

private noncomputable def pair (ρX : F ⊗[R] X ≃ₐ[F] Xb) (ρY : F ⊗[R] Y ≃ₐ[F] Yb) :
    F ⊗[R] (X ⊗[R] Y) ≃ₐ[F] Xb ⊗[F] Yb :=
  (κ R F X Y).trans (Algebra.TensorProduct.congr ρX ρY)

private theorem pair_tmul (ρX : F ⊗[R] X ≃ₐ[F] Xb) (ρY : F ⊗[R] Y ≃ₐ[F] Yb) (a : F) (x : X) (y : Y) :
    pair ρX ρY (a ⊗ₜ[R] (x ⊗ₜ[R] y)) = ρX (a ⊗ₜ[R] x) ⊗ₜ[F] ρY ((1 : F) ⊗ₜ[R] y) := by
  simp [pair, κ_tmul]

private theorem tmul_eq_smul_one_tmul (a : F) (x : X) : a ⊗ₜ[R] x = a • ((1 : F) ⊗ₜ[R] x) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem apply_tmul_eq_smul (ρX : F ⊗[R] X ≃ₐ[F] Xb) (a : F) (x : X) :
    ρX (a ⊗ₜ[R] x) = a • ρX ((1 : F) ⊗ₜ[R] x) := by
  rw [tmul_eq_smul_one_tmul, map_smul]

private theorem pair_bar_map {ρX : F ⊗[R] X ≃ₐ[F] Xb} {ρY : F ⊗[R] Y ≃ₐ[F] Yb}
    {ρX' : F ⊗[R] X' ≃ₐ[F] Xb'} {ρY' : F ⊗[R] Y' ≃ₐ[F] Yb'}
    {f : X →ₐ[R] X'} {g : Y →ₐ[R] Y'} {fb : Xb →ₐ[F] Xb'} {gb : Yb →ₐ[F] Yb'}
    (hf : ∀ z, ρX' (bar F f z) = fb (ρX z)) (hg : ∀ z, ρY' (bar F g z) = gb (ρY z))
    (z : F ⊗[R] (X ⊗[R] Y)) :
    pair ρX' ρY' (bar F (Algebra.TensorProduct.map f g) z) =
      Algebra.TensorProduct.map fb gb (pair ρX ρY z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul x y =>
      rw [bar_tmul, Algebra.TensorProduct.map_tmul, pair_tmul, pair_tmul,
        Algebra.TensorProduct.map_tmul, ← hf, ← hg, bar_tmul, bar_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pair_bar_assoc (ρX : F ⊗[R] X ≃ₐ[F] Xb) (ρY : F ⊗[R] Y ≃ₐ[F] Yb)
    (ρZ : F ⊗[R] Z ≃ₐ[F] Zb) (z : F ⊗[R] ((X ⊗[R] Y) ⊗[R] Z)) :
    pair ρX (pair ρY ρZ) (bar F (Algebra.TensorProduct.assoc R R R X Y Z).toAlgHom z) =
      Algebra.TensorProduct.assoc F F F Xb Yb Zb (pair (pair ρX ρY) ρZ z) := by
  have key : ∀ (a : F) (x : X) (y : Y) (c : Z),
      pair ρX (pair ρY ρZ) (bar F (Algebra.TensorProduct.assoc R R R X Y Z).toAlgHom
        (a ⊗ₜ[R] ((x ⊗ₜ[R] y) ⊗ₜ[R] c))) =
      Algebra.TensorProduct.assoc F F F Xb Yb Zb (pair (pair ρX ρY) ρZ
        (a ⊗ₜ[R] ((x ⊗ₜ[R] y) ⊗ₜ[R] c))) := by
    intro a x y c
    rw [bar_tmul, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.assoc_tmul,
      pair_tmul, pair_tmul, pair_tmul, pair_tmul, Algebra.TensorProduct.assoc_tmul]
  letI : Module R (Xb ⊗[F] (Yb ⊗[F] Zb)) := Module.compHom _ (algebraMap R F)
  haveI : IsScalarTower R F (Xb ⊗[F] (Yb ⊗[F] Zb)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module R ((Xb ⊗[F] Yb) ⊗[F] Zb) := Module.compHom _ (algebraMap R F)
  haveI : IsScalarTower R F ((Xb ⊗[F] Yb) ⊗[F] Zb) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let L₁ : F ⊗[R] ((X ⊗[R] Y) ⊗[R] Z) →ₗ[R] Xb ⊗[F] (Yb ⊗[F] Zb) :=
    ((pair ρX (pair ρY ρZ)).toLinearMap.restrictScalars R) ∘ₗ
      ((bar F (Algebra.TensorProduct.assoc R R R X Y Z).toAlgHom).toLinearMap.restrictScalars R)
  let L₂ : F ⊗[R] ((X ⊗[R] Y) ⊗[R] Z) →ₗ[R] Xb ⊗[F] (Yb ⊗[F] Zb) :=
    ((Algebra.TensorProduct.assoc F F F Xb Yb Zb).toLinearMap.restrictScalars R) ∘ₗ
      ((pair (pair ρX ρY) ρZ).toLinearMap.restrictScalars R)
  have hL : L₁ = L₂ := by
    refine TensorProduct.ext' fun a w => ?_
    have h3 : L₁ ∘ₗ TensorProduct.mk R F _ a = L₂ ∘ₗ TensorProduct.mk R F _ a :=
      TensorProduct.ext_threefold fun x y c => key a x y c
    exact LinearMap.congr_fun h3 w
  exact LinearMap.congr_fun hL z

private theorem bar_lmul (ρX : F ⊗[R] X ≃ₐ[F] Xb) (z : F ⊗[R] (X ⊗[R] X)) :
    ρX (bar F (Algebra.TensorProduct.lmul' R (S := X)) z) =
      Algebra.TensorProduct.lmul' F (S := Xb) (pair ρX ρX z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul x y =>
      rw [bar_tmul, Algebra.TensorProduct.lmul'_apply_tmul, pair_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pair_bar_comm (ρX : F ⊗[R] X ≃ₐ[F] Xb) (ρY : F ⊗[R] Y ≃ₐ[F] Yb)
    (z : F ⊗[R] (X ⊗[R] Y)) :
    pair ρY ρX (bar F (Algebra.TensorProduct.comm R X Y).toAlgHom z) =
      Algebra.TensorProduct.comm F Xb Yb (pair ρX ρY z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul x y =>
      rw [bar_tmul, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.comm_tmul,
        pair_tmul, pair_tmul, Algebra.TensorProduct.comm_tmul, apply_tmul_eq_smul ρY a y,
        apply_tmul_eq_smul ρX a x, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (R F) in

private noncomputable abbrev ρ0 : F ⊗[R] R ≃ₐ[F] F := Algebra.TensorProduct.rid R F F

private theorem pair_bar_lid_symm (ρX : F ⊗[R] X ≃ₐ[F] Xb) (z : F ⊗[R] X) :
    pair (ρ0 R F) ρX (bar F (Algebra.TensorProduct.lid R X).symm.toAlgHom z) =
      (Algebra.TensorProduct.lid F Xb).symm (ρX z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [bar_tmul, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.lid_symm_apply,
      pair_tmul, Algebra.TensorProduct.lid_symm_apply, Algebra.TensorProduct.rid_tmul, one_smul,
      apply_tmul_eq_smul ρX a x, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pair_bar_rid_symm (ρX : F ⊗[R] X ≃ₐ[F] Xb) (z : F ⊗[R] X) :
    pair ρX (ρ0 R F) (bar F (Algebra.TensorProduct.rid R R X).symm.toAlgHom z) =
      (Algebra.TensorProduct.rid F F Xb).symm (ρX z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [bar_tmul, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.rid_symm_apply,
      pair_tmul, Algebra.TensorProduct.rid_symm_apply, Algebra.TensorProduct.rid_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem bar_ofId (ρX : F ⊗[R] X ≃ₐ[F] Xb) (z : F ⊗[R] R) :
    ρX (bar F (Algebra.ofId R X) z) = Algebra.ofId F Xb (ρ0 R F z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a r =>
    rw [bar_tmul, Algebra.ofId_apply, Algebra.TensorProduct.rid_tmul, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
      tmul_eq_smul_one_tmul, ← Algebra.TensorProduct.one_def, map_smul, map_one]
  | add x y hx hy => simp only [map_add, hx, hy]

end BC

section Bridge

variable {F : Type*} [CommRing F] {A B C D : Type*} [CommRing A] [Algebra F A] [CommRing B]
  [Algebra F B] [CommRing C] [Algebra F C] [CommRing D] [Algebra F D]

private theorem algMap_apply_eq (f : A →ₐ[F] C) (g : B →ₐ[F] D) (z : A ⊗[F] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem algAssoc_apply_eq (z : (A ⊗[F] B) ⊗[F] C) :
    Algebra.TensorProduct.assoc F F F A B C z = _root_.TensorProduct.assoc F A B C z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, LinearEquiv.map_zero]
  | tmul v c =>
    induction v using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, LinearEquiv.map_zero]
    | tmul a b => rw [Algebra.TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Bridge

section BridgeBialgebra

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [Bialgebra F A]

private theorem assoc_map_comul_comul (w : A) :
    Algebra.TensorProduct.assoc F F F A A A (Algebra.TensorProduct.map (Bialgebra.comulAlgHom F A)
      (AlgHom.id F A) (Bialgebra.comulAlgHom F A w)) =
    Algebra.TensorProduct.map (AlgHom.id F A) (Bialgebra.comulAlgHom F A)
      (Bialgebra.comulAlgHom F A w) := by
  rw [algAssoc_apply_eq, algMap_apply_eq, algMap_apply_eq, Bialgebra.comulAlgHom_apply]
  exact Coalgebra.coassoc_apply w

private theorem map_counit_id_comul (w : A) :
    Algebra.TensorProduct.map (Bialgebra.counitAlgHom F A) (AlgHom.id F A)
      (Bialgebra.comulAlgHom F A w) = (Algebra.TensorProduct.lid F A).symm w := by
  rw [algMap_apply_eq, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.lid_symm_apply]
  exact Coalgebra.rTensor_counit_comul w

private theorem map_id_counit_comul (w : A) :
    Algebra.TensorProduct.map (AlgHom.id F A) (Bialgebra.counitAlgHom F A)
      (Bialgebra.comulAlgHom F A w) = (Algebra.TensorProduct.rid F F A).symm w := by
  rw [algMap_apply_eq, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.rid_symm_apply]
  exact Coalgebra.lTensor_counit_comul w

end BridgeBialgebra

section Antipode

variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [HopfAlgebra F A]

variable (F A) in

private noncomputable def antipodeAlgHom : A →ₐ[F] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode F) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

private theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom F A a = HopfAlgebra.antipode F a := rfl

private theorem lmul_map_antipode_id_comul (w : A) :
    Algebra.TensorProduct.lmul' F (S := A) (Algebra.TensorProduct.map (antipodeAlgHom F A)
      (AlgHom.id F A) (Bialgebra.comulAlgHom F A w)) =
    Algebra.ofId F A (Bialgebra.counitAlgHom F A w) := by
  rw [algMap_apply_eq, Bialgebra.comulAlgHom_apply, ← AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.lmul'_toLinearMap, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  exact HopfAlgebra.mul_antipode_rTensor_comul_apply (R := F) w

private theorem lmul_map_id_antipode_comul (w : A) :
    Algebra.TensorProduct.lmul' F (S := A) (Algebra.TensorProduct.map (AlgHom.id F A)
      (antipodeAlgHom F A) (Bialgebra.comulAlgHom F A w)) =
    Algebra.ofId F A (Bialgebra.counitAlgHom F A w) := by
  rw [algMap_apply_eq, Bialgebra.comulAlgHom_apply, ← AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.lmul'_toLinearMap, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  exact HopfAlgebra.mul_antipode_lTensor_comul_apply (R := F) w

end Antipode

section Lift

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
variable {H : Type u} [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
  [Algebra.FormallyEtale 𝓞 H]

private theorem uniq (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {T : Type u} [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    {f g : H →ₐ[𝓞] T} (h : ∀ z, bar (ZMod p) f z = bar (ZMod p) g z) : f = g :=
  (Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp p hp hker H T
    (bar (ZMod p) g)).unique (AlgHom.ext h) rfl

private theorem exists_lift (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (T : Type u) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ψ : ZMod p ⊗[𝓞] H →ₐ[ZMod p] ZMod p ⊗[𝓞] T) :
    ∃ f : H →ₐ[𝓞] T, ∀ z, bar (ZMod p) f z = ψ z := by
  obtain ⟨f, hf, -⟩ :=
    Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp p hp hker H T ψ
  exact ⟨f, fun z => by rw [← hf]⟩

end Lift

end HopfLift

open HopfLift in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Hbar : Type v) [CommRing Hbar] [HopfAlgebra (ZMod p) Hbar] [Coalgebra.IsCocomm (ZMod p) Hbar]
    [Module.Finite (ZMod p) Hbar] [IsReduced Hbar] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H),
      Module.finrank 𝓞 H = Module.finrank (ZMod p) Hbar ∧
      Nonempty ((ZMod p ⊗[𝓞] H) ≃ₐc[ZMod p] Hbar) := by
  classical
  obtain ⟨H, _instCR, _instAlg, _instFree, _instFin, _instEt, hrank, ⟨θ⟩⟩ :=
    Algebra.FormallyEtale.exists_baseChange_algEquiv_of_isReduced_zmodp p hp hker Hbar

  have idsq : ∀ z, θ (bar (ZMod p) (AlgHom.id 𝓞 H) z) = (AlgHom.id (ZMod p) Hbar) (θ z) :=
    fun z => by rw [bar_id_apply]; rfl

  obtain ⟨Δ, hΔ'⟩ := exists_lift p hp hker (H ⊗[𝓞] H)
    ((pair θ θ).symm.toAlgHom.comp ((Bialgebra.comulAlgHom (ZMod p) Hbar).comp θ.toAlgHom))
  have hΔ : ∀ z, pair θ θ (bar (ZMod p) Δ z) = Bialgebra.comulAlgHom (ZMod p) Hbar (θ z) := by
    intro z
    rw [hΔ', AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]

  obtain ⟨ε, hε'⟩ := exists_lift p hp hker 𝓞
    ((ρ0 𝓞 (ZMod p)).symm.toAlgHom.comp ((Bialgebra.counitAlgHom (ZMod p) Hbar).comp θ.toAlgHom))
  have hε : ∀ z, ρ0 𝓞 (ZMod p) (bar (ZMod p) ε z) = Bialgebra.counitAlgHom (ZMod p) Hbar (θ z) := by
    intro z
    rw [hε', AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]

  obtain ⟨S, hS'⟩ := exists_lift p hp hker H
    (θ.symm.toAlgHom.comp ((antipodeAlgHom (ZMod p) Hbar).comp θ.toAlgHom))
  have hS : ∀ z, θ (bar (ZMod p) S z) = antipodeAlgHom (ZMod p) Hbar (θ z) := by
    intro z
    rw [hS', AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.apply_symm_apply]

  have h_coassoc : (Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 H H H).toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (.id 𝓞 H)).comp Δ)
      = (Algebra.TensorProduct.map (.id 𝓞 H) Δ).comp Δ := by
    apply uniq p hp hker
    intro z
    apply (pair θ (pair θ θ)).injective
    rw [bar_comp_apply, bar_comp_apply, pair_bar_assoc, pair_bar_map hΔ idsq, hΔ,
      bar_comp_apply, pair_bar_map idsq hΔ, hΔ]
    exact assoc_map_comul_comul (θ z)

  have h_rTensor : (Algebra.TensorProduct.map ε (.id 𝓞 H)).comp Δ
      = (Algebra.TensorProduct.lid 𝓞 H).symm := by
    apply uniq p hp hker
    intro z
    apply (pair (ρ0 𝓞 (ZMod p)) θ).injective
    rw [bar_comp_apply, pair_bar_map hε idsq, hΔ, pair_bar_lid_symm]
    exact map_counit_id_comul (θ z)
  have h_lTensor : (Algebra.TensorProduct.map (.id 𝓞 H) ε).comp Δ
      = (Algebra.TensorProduct.rid 𝓞 𝓞 H).symm := by
    apply uniq p hp hker
    intro z
    apply (pair θ (ρ0 𝓞 (ZMod p))).injective
    rw [bar_comp_apply, pair_bar_map idsq hε, hΔ, pair_bar_rid_symm]
    exact map_id_counit_comul (θ z)
  letI _instBi : Bialgebra 𝓞 H := Bialgebra.ofAlgHom Δ ε h_coassoc h_rTensor h_lTensor

  have hA4 : (Algebra.TensorProduct.lmul' 𝓞 (S := H)).comp
      ((Algebra.TensorProduct.map S (.id 𝓞 H)).comp Δ) = (Algebra.ofId 𝓞 H).comp ε := by
    apply uniq p hp hker
    intro z
    apply θ.injective
    rw [bar_comp_apply, bar_comp_apply, bar_lmul, pair_bar_map hS idsq, hΔ, bar_comp_apply,
      bar_ofId, hε]
    exact lmul_map_antipode_id_comul (θ z)
  have hA5 : (Algebra.TensorProduct.lmul' 𝓞 (S := H)).comp
      ((Algebra.TensorProduct.map (.id 𝓞 H) S).comp Δ) = (Algebra.ofId 𝓞 H).comp ε := by
    apply uniq p hp hker
    intro z
    apply θ.injective
    rw [bar_comp_apply, bar_comp_apply, bar_lmul, pair_bar_map idsq hS, hΔ, bar_comp_apply,
      bar_ofId, hε]
    exact lmul_map_id_antipode_comul (θ z)
  have hrT : (Algebra.TensorProduct.map S (AlgHom.id 𝓞 H)).toLinearMap
      = S.toLinearMap.rTensor H := TensorProduct.ext' fun _ _ => rfl
  have hlT : (Algebra.TensorProduct.map (AlgHom.id 𝓞 H) S).toLinearMap
      = S.toLinearMap.lTensor H := TensorProduct.ext' fun _ _ => rfl
  letI _instHopf : HopfAlgebra 𝓞 H :=
    { antipode := S.toLinearMap
      mul_antipode_rTensor_comul := by
        have h := congrArg AlgHom.toLinearMap hA4
        rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
          hrT, AlgHom.comp_toLinearMap] at h
        exact h
      mul_antipode_lTensor_comul := by
        have h := congrArg AlgHom.toLinearMap hA5
        rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap,
          hlT, AlgHom.comp_toLinearMap] at h
        exact h }

  have h6 : (Algebra.TensorProduct.comm 𝓞 H H).toAlgHom.comp Δ = Δ := by
    apply uniq p hp hker
    intro z
    apply (pair θ θ).injective
    rw [bar_comp_apply, pair_bar_comm, hΔ]
    exact Coalgebra.comm_comul (ZMod p) (θ z)
  haveI _instCocomm : Coalgebra.IsCocomm 𝓞 H := ⟨congrArg AlgHom.toLinearMap h6⟩

  have hcomulBC : ∀ z : ZMod p ⊗[𝓞] H,
      Coalgebra.comul (R := ZMod p) z = κ 𝓞 (ZMod p) H H (bar (ZMod p) Δ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a h =>
      rw [TensorProduct.comul_tmul, bar_tmul]
      show TensorProduct.AlgebraTensorModule.tensorTensorTensorComm 𝓞 (ZMod p) 𝓞 (ZMod p) (ZMod p)
          (ZMod p) H H (((1 : ZMod p) ⊗ₜ[ZMod p] a) ⊗ₜ[𝓞] Δ h) = κ 𝓞 (ZMod p) H H (a ⊗ₜ[𝓞] Δ h)
      generalize Δ h = w
      induction w using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
      | tmul x y =>
        rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, κ_tmul,
          tmul_eq_smul_one_tmul a y, tmul_eq_smul_one_tmul a x, TensorProduct.smul_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcounitBC : ∀ z : ZMod p ⊗[𝓞] H,
      Coalgebra.counit (R := ZMod p) z = ρ0 𝓞 (ZMod p) (bar (ZMod p) ε z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a h =>
      rw [TensorProduct.counit_tmul, bar_tmul, Algebra.TensorProduct.rid_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hθcounit : (Bialgebra.counitAlgHom (ZMod p) Hbar).comp θ.toAlgHom
      = Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[𝓞] H) := by
    apply AlgHom.ext
    intro z
    rw [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Bialgebra.counitAlgHom_apply,
      Bialgebra.counitAlgHom_apply, hcounitBC, hε, Bialgebra.counitAlgHom_apply]
  have hθcomul : (Algebra.TensorProduct.map θ.toAlgHom θ.toAlgHom).comp
      (Bialgebra.comulAlgHom (ZMod p) (ZMod p ⊗[𝓞] H))
      = (Bialgebra.comulAlgHom (ZMod p) Hbar).comp θ.toAlgHom := by
    apply AlgHom.ext
    intro z
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Bialgebra.comulAlgHom_apply,
      hcomulBC, ← hΔ]
    rfl
  let θc : (ZMod p ⊗[𝓞] H) →ₐc[ZMod p] Hbar := BialgHom.ofAlgHom θ.toAlgHom hθcounit hθcomul
  have θe : (ZMod p ⊗[𝓞] H) ≃ₐc[ZMod p] Hbar := BialgEquiv.ofBijective θc θ.bijective
  exact ⟨H, _instCR, _instHopf, _instCocomm, _instFree, _instFin, _instEt, hrank, ⟨θe⟩⟩

end S_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp
end P2MW
export P2MW.S_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp (solution)
