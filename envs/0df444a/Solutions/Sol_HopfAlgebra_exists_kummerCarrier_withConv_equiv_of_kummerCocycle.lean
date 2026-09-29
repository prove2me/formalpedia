-- Prove2me | solution 1 for HopfAlgebra.exists_kummerCarrier_withConv_equiv_of_kummerCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dafcab38-33fa-53e2-a017-b90e699fa04d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul"
p2m_open "HopfAlgebra"

universe u v

structure KummerDatum (O : Type u) [CommRing O] (n : ℕ) (Λ : Type v) [AddCommGroup Λ] where

  u : Λ → O

  c : Λ → Λ → O
  isUnit_u : ∀ l, IsUnit (u l)
  u_zero : u 0 = 1
  c_pow_mul : ∀ l l', c l l' ^ n * (u l * u l') = u (l + l')
  c_zero_left : ∀ l, c 0 l = 1
  c_comm : ∀ l l', c l l' = c l' l
  c_assoc : ∀ l l' l'', c l l' * c (l + l') l'' = c l (l' + l'') * c l' l''

namespace KummerDatum

variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type v} [AddCommGroup Λ]
variable (D : KummerDatum O n Λ)

theorem c_zero_right (l : Λ) : D.c l 0 = 1 := by rw [D.c_comm, D.c_zero_left]

theorem isUnit_c (hn : n ≠ 0) (l l' : Λ) : IsUnit (D.c l l') := by
  have h := D.c_pow_mul l l'
  have hu : IsUnit (D.c l l' ^ n) := by
    have := D.isUnit_u (l + l')
    rw [← h] at this
    exact isUnit_of_mul_isUnit_left this
  exact (isUnit_pow_iff hn).mp hu

noncomputable abbrev kpoly (l : Λ) : O[X] := X ^ n - C (D.u l)

theorem kpoly_monic [Nontrivial O] (hn : n ≠ 0) (l : Λ) : (D.kpoly l).Monic :=
  Polynomial.monic_X_pow_sub_C (D.u l) hn

noncomputable abbrev A (l : Λ) : Type u := AdjoinRoot (D.kpoly l)

theorem free_A [Nontrivial O] (hn : n ≠ 0) (l : Λ) : Module.Free O (D.A l) := (D.kpoly_monic hn l).free_adjoinRoot
theorem finite_A [Nontrivial O] (hn : n ≠ 0) (l : Λ) : Module.Finite O (D.A l) := (D.kpoly_monic hn l).finite_adjoinRoot

noncomputable abbrev Carrier : Type (max u v) := Π l : Λ, D.A l

noncomputable abbrev z (l : Λ) : D.A l := AdjoinRoot.root (D.kpoly l)

theorem z_pow (l : Λ) : D.z l ^ n = algebraMap O (D.A l) (D.u l) := by
  have h : (Polynomial.aeval (D.z l)) (D.kpoly l) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

noncomputable def ε : D.Carrier →ₐ[O] O :=
  (AdjoinRoot.liftAlgHom (D.kpoly 0) (Algebra.ofId O O) 1
    (by simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C])).comp
    (Pi.evalAlgHom _ _ 0)

variable [Fintype Λ] [DecidableEq Λ]

noncomputable def piPiEquiv :
    D.Carrier ⊗[O] D.Carrier ≃ₐ[O] Π a : Λ, Π b : Λ, D.A a ⊗[O] D.A b :=
  (Algebra.TensorProduct.comm O _ _).trans <|
    (Algebra.TensorProduct.piRight O O D.Carrier D.A).trans <|
      AlgEquiv.piCongrRight fun a =>
        (Algebra.TensorProduct.comm O _ _).trans <|
          Algebra.TensorProduct.piRight O O (D.A a) D.A

theorem piPiEquiv_tmul (f g : D.Carrier) (a b : Λ) :
    D.piPiEquiv (f ⊗ₜ g) a b = f a ⊗ₜ g b := by
  simp [piPiEquiv, Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.comm_tmul]

noncomputable def μ (a b : Λ) : D.Carrier →ₐ[O] D.A a ⊗[O] D.A b :=
  (AdjoinRoot.liftAlgHom (D.kpoly (a + b)) (Algebra.ofId _ _)
    (D.c a b • (D.z a ⊗ₜ D.z b))
    (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
        _root_.smul_pow, Algebra.TensorProduct.tmul_pow, z_pow]
      rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
        Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
        TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
        ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
      rfl)).comp
    (Pi.evalAlgHom _ _ (a + b))

noncomputable def Δ : D.Carrier →ₐ[O] D.Carrier ⊗[O] D.Carrier :=
  D.piPiEquiv.symm.toAlgHom.comp
    (Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => D.μ a b)

variable {L : Type*} [CommRing L] [Algebra O L]

omit [Fintype Λ] [DecidableEq Λ] in

noncomputable def evalAt (l : Λ) (w : L) (hw : w ^ n = algebraMap O L (D.u l)) :
    D.Carrier →ₐ[O] L :=
  (AdjoinRoot.liftAlgHom (D.kpoly l) (Algebra.ofId O L) w
    (by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero]
      exact hw.trans rfl)).comp
    (Pi.evalAlgHom _ _ l)

omit [Fintype Λ] [DecidableEq Λ] in
theorem evalAt_apply_z' (l : Λ) (w : L) (hw : w ^ n = algebraMap O L (D.u l)) (h : D.Carrier)
    (q : O[X]) (hq : h l = AdjoinRoot.mk _ q) :
    D.evalAt l w hw h = Polynomial.aeval w q := by
  unfold evalAt
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply]
  rw [hq, AdjoinRoot.liftAlgHom_mk]
  rfl

theorem exists_polyLift (h : D.Carrier) (l : Λ) : ∃ q : O[X], h l = AdjoinRoot.mk _ q :=
  AdjoinRoot.mk_surjective (h l) |>.imp fun _ hq => hq.symm

end KummerDatum

end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul"
p2m_open "HopfAlgebra"

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem KummerDatum.comul_coassoc :
    (Algebra.TensorProduct.assoc O O O
        (D.Carrier) (D.Carrier) (D.Carrier)).toAlgHom.comp
      ((Algebra.TensorProduct.map (D.Δ) (.id O (D.Carrier))).comp (D.Δ))
      = (Algebra.TensorProduct.map (.id O (D.Carrier)) (D.Δ)).comp (D.Δ) := by

  have hlift_root : ∀ {T : Type u} [CommRing T] [Algebra O T] (j : Λ) (w : T) (hwj),
      AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId O T) w hwj
        (AdjoinRoot.root (D.kpoly j)) = w := by
    intro T _ _ j w hwj
    rw [show AdjoinRoot.root (D.kpoly j) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]

  have hΔ_comp : ∀ (h : D.Carrier) (a b : Λ),
      D.piPiEquiv (D.Δ h) a b = D.μ a b h := fun h a b => by
    have hrfl : D.Δ h = (D.piPiEquiv).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => D.μ a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl

  have hmap_eval : ∀ (a b : Λ) (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
        (Pi.evalAlgHom O D.A b) y = D.piPiEquiv y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, D.piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

  let E3 : D.Carrier ⊗[O] (D.Carrier ⊗[O] D.Carrier) ≃ₐ[O]
      Π a : Λ, Π b : Λ, Π c : Λ,
        D.A a ⊗[O] (D.A b ⊗[O] D.A c) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl) (D.piPiEquiv)).trans <|
    (Algebra.TensorProduct.comm O _ _).trans <|
    (Algebra.TensorProduct.piRight O O _ D.A).trans <|
    AlgEquiv.piCongrRight fun a =>
      (Algebra.TensorProduct.comm O _ _).trans <|
      (Algebra.TensorProduct.piRight O O (D.A a)
        (fun b => Π c : Λ, D.A b ⊗[O] D.A c)).trans <|
      AlgEquiv.piCongrRight fun b =>
        Algebra.TensorProduct.piRight O O (D.A a)
          (fun c => D.A b ⊗[O] D.A c)

  have hE3_zero : E3 0 = 0 := map_zero E3
  have hE3_add : ∀ x y, E3 (x + y) = E3 x + E3 y := fun x y => map_add E3 x y

  have hcongr_tmul : ∀ (f : D.Carrier) (y : D.Carrier ⊗[O] D.Carrier),
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := O) (A₁ := D.Carrier))
        (D.piPiEquiv)) (f ⊗ₜ y) = f ⊗ₜ (D.piPiEquiv y) := fun f y => rfl

  have hE3_tmul : ∀ (f g k : D.Carrier) (a b c : Λ),
      E3 (f ⊗ₜ (g ⊗ₜ k)) a b c = (f a) ⊗ₜ ((g b) ⊗ₜ (k c)) := by
    intro f g k a b c
    simp only [E3, AlgEquiv.trans_apply, hcongr_tmul, D.piPiEquiv_tmul,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.piRight_tmul,
      AlgEquiv.piCongrRight_apply]

  have hE3 : ∀ (y : D.Carrier ⊗[O] (D.Carrier ⊗[O] D.Carrier)) (a b c : Λ),
      E3 y a b c = Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A b)
          (Pi.evalAlgHom O D.A c)) y := by
    intro y a b c
    induction y using TensorProduct.induction_on with
    | zero => rw [hE3_zero]; simp only [Pi.zero_apply, map_zero]
    | tmul f yy =>
      induction yy using TensorProduct.induction_on with
      | zero =>
        rw [TensorProduct.tmul_zero, hE3_zero]
        simp only [Pi.zero_apply, map_zero]
      | tmul g k =>
        rw [hE3_tmul]
        simp only [Algebra.TensorProduct.map_tmul, Pi.evalAlgHom_apply]
      | add y1 y2 hy1 hy2 =>
        rw [TensorProduct.tmul_add, hE3_add]
        simp only [Pi.add_apply, hy1, hy2, map_add]
    | add y1 y2 hy1 hy2 =>
      rw [hE3_add]; simp only [Pi.add_apply, hy1, hy2, map_add]

  have hcfac_2cocycle : ∀ (a b c : Λ),
      D.c (a+b) c * D.c a b = D.c a (b+c) * D.c b c := by
    intro a b c
    rw [mul_comm]
    exact D.c_assoc a b c

  have hμ_at_j : ∀ (a' b' j : Λ) (hj : a' + b' = j) (h : D.Carrier),
      D.μ a' b' h = AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId _ _)
        (D.c a' b' • (D.z a' ⊗ₜ D.z b'))
        (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow, ← hj]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a'),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b'),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl) (h j) := by
    intro a' b' j hj h
    subst hj
    rfl

  apply AlgHom.ext; intro h
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  apply E3.injective
  funext a b c
  rw [hE3, hE3]
  show Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
      (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A b)
        (Pi.evalAlgHom O D.A c))
      (Algebra.TensorProduct.assoc O O O (D.Carrier) (D.Carrier) (D.Carrier)
        ((Algebra.TensorProduct.map (D.Δ) (AlgHom.id O (D.Carrier))) (D.Δ h)))
    = Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
      (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A b)
        (Pi.evalAlgHom O D.A c))
      ((Algebra.TensorProduct.map (AlgHom.id O (D.Carrier)) (D.Δ)) (D.Δ h))

  have hR1 : ∀ (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A b)
          (Pi.evalAlgHom O D.A c))
        (Algebra.TensorProduct.map (AlgHom.id O (D.Carrier)) (D.Δ) y)
      = Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a) (D.μ b c) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Pi.evalAlgHom_apply]
      rw [hmap_eval, hΔ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  let μlift_bc : D.A (b+c) →ₐ[O] D.A b ⊗[O] D.A c :=
    AdjoinRoot.liftAlgHom (D.kpoly (b+c)) (Algebra.ofId _ _)
      (D.c b c • (D.z b ⊗ₜ D.z c))
      (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A c),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
  have hR2 : ∀ (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a) (D.μ b c) y
      = Algebra.TensorProduct.map (AlgHom.id O (D.A a)) μlift_bc
          (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
            (Pi.evalAlgHom O D.A (b+c)) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Pi.evalAlgHom_apply]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  have hL1 : ∀ (y : (D.Carrier ⊗[O] D.Carrier) ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
        (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A b)
          (Pi.evalAlgHom O D.A c))
        (Algebra.TensorProduct.assoc O O O (D.Carrier) (D.Carrier) (D.Carrier) y)
      = Algebra.TensorProduct.assoc O O O (D.A a) (D.A b) (D.A c)
          (Algebra.TensorProduct.map
            (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
              (Pi.evalAlgHom O D.A b))
            (Pi.evalAlgHom O D.A c) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul xy zz =>
      induction xy using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | tmul xx yy =>
        simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.map_tmul,
          Pi.evalAlgHom_apply]
      | add x1 x2 hx1 hx2 =>
        simp only [TensorProduct.add_tmul, map_add, hx1, hx2]
    | add y1 y2 hy1 hy2 => simp only [map_add, hy1, hy2]
  have hL2 : ∀ (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map
        (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a)
          (Pi.evalAlgHom O D.A b))
        (Pi.evalAlgHom O D.A c)
        (Algebra.TensorProduct.map (D.Δ) (AlgHom.id O (D.Carrier)) y)
      = Algebra.TensorProduct.map (D.μ a b) (Pi.evalAlgHom O D.A c) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Pi.evalAlgHom_apply]
      rw [hmap_eval, hΔ_comp]
    | add x y hx hy => simp only [map_add, hx, hy]
  let μlift_ab : D.A (a+b) →ₐ[O] D.A a ⊗[O] D.A b :=
    AdjoinRoot.liftAlgHom (D.kpoly (a+b)) (Algebra.ofId _ _)
      (D.c a b • (D.z a ⊗ₜ D.z b))
      (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
  have hL3 : ∀ (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (D.μ a b) (Pi.evalAlgHom O D.A c) y
      = Algebra.TensorProduct.map μlift_ab (AlgHom.id O (D.A c))
          (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A (a+b))
            (Pi.evalAlgHom O D.A c) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul f g => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Pi.evalAlgHom_apply]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  conv_rhs => rw [hR1, hR2, hmap_eval, hΔ_comp]
  conv_lhs => rw [hL1, hL2, hL3, hmap_eval, hΔ_comp]

  set j := a + (b + c) with hj_def
  have hj_L : (a+b)+c = j := by rw [hj_def, add_assoc]
  have hj_R : a+(b+c) = j := by rw [hj_def]
  let liftL : D.A j →ₐ[O] D.A (a+b) ⊗[O] D.A c :=
    AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId _ _)
      (D.c (a+b) c • (D.z (a+b) ⊗ₜ D.z c))
      (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow, ← hj_L]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A (a+b)),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A c),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
  let liftR : D.A j →ₐ[O] D.A a ⊗[O] D.A (b+c) :=
    AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId _ _)
      (D.c a (b+c) • (D.z a ⊗ₜ D.z (b+c)))
      (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow, ← hj_R]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A (b+c)),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
  have hμL : D.μ (a+b) c h = liftL (h j) := hμ_at_j (a+b) c j hj_L h
  have hμR : D.μ a (b+c) h = liftR (h j) := hμ_at_j a (b+c) j hj_R h
  rw [hμL, hμR]

  have hliftL_root : liftL (AdjoinRoot.root (D.kpoly j))
      = D.c (a+b) c • (D.z (a+b) ⊗ₜ D.z c) := hlift_root j _ _
  have hliftR_root : liftR (AdjoinRoot.root (D.kpoly j))
      = D.c a (b+c) • (D.z a ⊗ₜ D.z (b+c)) := hlift_root j _ _
  have hμab_root : μlift_ab (D.z (a+b))
      = D.c a b • (D.z a ⊗ₜ D.z b) := hlift_root (a+b) _ _
  have hμbc_root : μlift_bc (D.z (b+c))
      = D.c b c • (D.z b ⊗ₜ D.z c) := hlift_root (b+c) _ _
  have key :
      (Algebra.TensorProduct.assoc O O O
        (D.A a) (D.A b) (D.A c)).toAlgHom.comp
        ((Algebra.TensorProduct.map μlift_ab (AlgHom.id O (D.A c))).comp liftL)
      = (Algebra.TensorProduct.map (AlgHom.id O (D.A a)) μlift_bc).comp liftR := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    show (Algebra.TensorProduct.assoc O O O (D.A a) (D.A b) (D.A c))
        ((Algebra.TensorProduct.map μlift_ab (AlgHom.id O (D.A c)))
          (liftL (AdjoinRoot.root (D.kpoly j))))
      = (Algebra.TensorProduct.map (AlgHom.id O (D.A a)) μlift_bc)
          (liftR (AdjoinRoot.root (D.kpoly j)))
    rw [hliftL_root, hliftR_root]

    rw [show (Algebra.TensorProduct.map μlift_ab (AlgHom.id O (D.A c)))
          (D.c (a+b) c • (D.z (a+b) ⊗ₜ D.z c))
        = D.c (a+b) c • (μlift_ab (D.z (a+b)) ⊗ₜ D.z c) from by
          rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply],
      hμab_root]

    rw [show (Algebra.TensorProduct.map (AlgHom.id O (D.A a)) μlift_bc)
          (D.c a (b+c) • (D.z a ⊗ₜ D.z (b+c)))
        = D.c a (b+c) • (D.z a ⊗ₜ μlift_bc (D.z (b+c))) from by
          rw [map_smul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply],
      hμbc_root]

    rw [show ((D.c a b • (D.z a ⊗ₜ D.z b)) ⊗ₜ[O] D.z c
          : (D.A a ⊗[O] D.A b) ⊗[O] D.A c)
        = D.c a b • ((D.z a ⊗ₜ D.z b) ⊗ₜ D.z c) from rfl,
      map_smul, map_smul, Algebra.TensorProduct.assoc_tmul, smul_smul]
    rw [show ((D.z a) ⊗ₜ[O] (D.c b c • (D.z b ⊗ₜ D.z c))
          : D.A a ⊗[O] (D.A b ⊗[O] D.A c))
        = D.c b c • (D.z a ⊗ₜ (D.z b ⊗ₜ D.z c)) from
          TensorProduct.tmul_smul _ _ _,
      smul_smul]
    rw [hcfac_2cocycle a b c]
  exact DFunLike.congr_fun key (h j)

end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul"
p2m_open "HopfAlgebra"

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

set_option maxHeartbeats 6400000 in

theorem KummerDatum.bialgebra_axioms :
    ((Algebra.TensorProduct.assoc O O O
        (D.Carrier) (D.Carrier) (D.Carrier)).toAlgHom.comp
      ((Algebra.TensorProduct.map (D.Δ) (.id O (D.Carrier))).comp (D.Δ))
      = (Algebra.TensorProduct.map (.id O (D.Carrier)) (D.Δ)).comp (D.Δ)) ∧
    ((Algebra.TensorProduct.map (D.ε) (.id O (D.Carrier))).comp (D.Δ)
      = (Algebra.TensorProduct.lid O (D.Carrier)).symm) ∧
    ((Algebra.TensorProduct.map (.id O (D.Carrier)) (D.ε)).comp (D.Δ)
      = (Algebra.TensorProduct.rid O O (D.Carrier)).symm) ∧
    (∀ h, (TensorProduct.comm O (D.Carrier) (D.Carrier)) (D.Δ h) = D.Δ h) := by

  have hΔ_comp : ∀ (h : D.Carrier) (a b : Λ),
      D.piPiEquiv (D.Δ h) a b = D.μ a b h := fun h a b => by
    have hrfl : D.Δ h = (D.piPiEquiv).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => D.μ a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl

  have hmap_eval : ∀ (a b : Λ) (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a) (Pi.evalAlgHom O D.A b) y
        = D.piPiEquiv y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, D.piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]

  have hcomm_piPi : ∀ (y : D.Carrier ⊗[O] D.Carrier) (a b : Λ),
      D.piPiEquiv (TensorProduct.comm O (D.Carrier) (D.Carrier) y) a b
        = Algebra.TensorProduct.comm O (D.A b) (D.A a) (D.piPiEquiv y b a) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul, D.piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

  have hcfac_zero : ∀ k : Λ, D.c 0 k = 1 ∧ D.c k 0 = 1 := fun k => ⟨D.c_zero_left k, D.c_zero_right k⟩

  have hcfac_symm : ∀ a b : Λ, D.c a b = D.c b a := fun a b => D.c_comm a b

  have hμ_at_j : ∀ (a b j : Λ) (hj : a + b = j) (h : D.Carrier),
      D.μ a b h = AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId _ _)
        (D.c a b • (D.z a ⊗ₜ D.z b))
        (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow, ← hj]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl) (h j) := by
    intro a b j hj h
    subst hj
    rfl

  have hlift_root : ∀ {T : Type u} [CommRing T] [Algebra O T] (j : Λ) (w : T) (hwj),
      AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId O T) w hwj
        (AdjoinRoot.root (D.kpoly j)) = w := by
    intro T _ _ j w hwj
    rw [show AdjoinRoot.root (D.kpoly j) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  refine ⟨D.comul_coassoc, ?_, ?_, ?_⟩

  · apply AlgHom.ext; intro h
    apply (Algebra.TensorProduct.lid O (D.Carrier)).injective
    conv_rhs => rw [show (↑(Algebra.TensorProduct.lid O (D.Carrier)).symm :
        D.Carrier →ₐ[O] _) h = (Algebra.TensorProduct.lid O (D.Carrier)).symm h from rfl,
      AlgEquiv.apply_symm_apply]
    simp only [AlgHom.comp_apply]
    funext k
    let εlift₀ : D.A 0 →ₐ[O] O :=
      AdjoinRoot.liftAlgHom (D.kpoly 0) (Algebra.ofId O O) 1
        (by simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X])

    have hlid_k : ∀ (y : D.Carrier ⊗[O] D.Carrier),
        (Algebra.TensorProduct.lid O (D.Carrier) (Algebra.TensorProduct.map (D.ε)
          (AlgHom.id O (D.Carrier)) y)) k
        = Algebra.TensorProduct.lmul' O
            (Algebra.TensorProduct.map ((Algebra.ofId O (D.A k)).comp εlift₀)
              (AlgHom.id O (D.A k))
              (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A 0)
                (Pi.evalAlgHom O D.A k) y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f g =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lid_tmul,
          Pi.smul_apply, AlgHom.comp_apply, Algebra.ofId_apply, Pi.evalAlgHom_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, Algebra.smul_def]
        rfl
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    rw [hlid_k, hmap_eval, hΔ_comp,
      hμ_at_j 0 k k (zero_add k) h]

    set x := h k
    let μlift0k : D.A k →ₐ[O] D.A 0 ⊗[O] D.A k :=
      AdjoinRoot.liftAlgHom (D.kpoly k) (Algebra.ofId _ _)
        (D.c 0 k • (D.z 0 ⊗ₜ D.z k))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A 0),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A k),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul, zero_add,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have key : (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map ((Algebra.ofId O (D.A k)).comp εlift₀)
          (AlgHom.id O (D.A k))).comp μlift0k)
        = AlgHom.id O (D.A k) := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [hlift_root, (hcfac_zero k).1, one_smul, Algebra.TensorProduct.map_tmul,
        AlgHom.comp_apply, hlift_root, map_one, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
    exact DFunLike.congr_fun key x

  · apply AlgHom.ext; intro h
    apply (Algebra.TensorProduct.rid O O (D.Carrier)).injective
    conv_rhs => rw [show (↑(Algebra.TensorProduct.rid O O (D.Carrier)).symm :
        D.Carrier →ₐ[O] _) h = (Algebra.TensorProduct.rid O O (D.Carrier)).symm h
        from rfl, AlgEquiv.apply_symm_apply]
    simp only [AlgHom.comp_apply]
    funext k
    let εlift₀ : D.A 0 →ₐ[O] O :=
      AdjoinRoot.liftAlgHom (D.kpoly 0) (Algebra.ofId O O) 1
        (by simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X])
    have hrid_k : ∀ (y : D.Carrier ⊗[O] D.Carrier),
        (Algebra.TensorProduct.rid O O (D.Carrier) (Algebra.TensorProduct.map
          (AlgHom.id O (D.Carrier)) (D.ε) y)) k
        = Algebra.TensorProduct.lmul' O
            (Algebra.TensorProduct.map (AlgHom.id O (D.A k))
              ((Algebra.ofId O (D.A k)).comp εlift₀)
              (Algebra.TensorProduct.map (Pi.evalAlgHom O D.A k)
                (Pi.evalAlgHom O D.A 0) y)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f g =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
          Pi.smul_apply, AlgHom.comp_apply, Algebra.ofId_apply, Pi.evalAlgHom_apply,
          Algebra.TensorProduct.lmul'_apply_tmul, Algebra.smul_def, mul_comm]
        rfl
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    rw [hrid_k, hmap_eval, hΔ_comp,
      hμ_at_j k 0 k (add_zero k) h]
    set x := h k
    let μliftk0 : D.A k →ₐ[O] D.A k ⊗[O] D.A 0 :=
      AdjoinRoot.liftAlgHom (D.kpoly k) (Algebra.ofId _ _)
        (D.c k 0 • (D.z k ⊗ₜ D.z 0))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A k),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A 0),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul, add_zero,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have key : (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map (AlgHom.id O (D.A k))
          ((Algebra.ofId O (D.A k)).comp εlift₀)).comp μliftk0)
        = AlgHom.id O (D.A k) := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [hlift_root, (hcfac_zero k).2, one_smul, Algebra.TensorProduct.map_tmul,
        AlgHom.comp_apply, hlift_root, map_one, AlgHom.id_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
    exact DFunLike.congr_fun key x

  · intro h
    apply (D.piPiEquiv).injective
    funext a b
    rw [hcomm_piPi, hΔ_comp, hΔ_comp]

    have hvba : a + b = b + a := add_comm a b
    let μliftba : D.A (b+a) →ₐ[O] D.A b ⊗[O] D.A a :=
      AdjoinRoot.liftAlgHom (D.kpoly (b+a)) (Algebra.ofId _ _)
        (D.c b a • (D.z b ⊗ₜ D.z a))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    let μliftab : D.A (b+a) →ₐ[O] D.A a ⊗[O] D.A b :=
      AdjoinRoot.liftAlgHom (D.kpoly (b+a)) (Algebra.ofId _ _)
        (D.c a b • (D.z a ⊗ₜ D.z b))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A a),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A b),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul, add_comm a b,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have hμba : D.μ b a h = μliftba (h (b+a)) := hμ_at_j b a (b+a) rfl h
    have hμab : D.μ a b h = μliftab (h (b+a)) := hμ_at_j a b (b+a) hvba h
    rw [hμba, hμab]
    have key : (Algebra.TensorProduct.comm O (D.A b) (D.A a)).toAlgHom.comp μliftba
        = μliftab := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
      rw [hlift_root, map_smul]
      show D.c b a • (D.z a ⊗ₜ[O] D.z b) = μliftab (AdjoinRoot.root (D.kpoly (b+a)))
      rw [hlift_root, hcfac_symm]
    exact DFunLike.congr_fun key (h (b+a))

end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul"
p2m_open "HopfAlgebra"

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

set_option maxHeartbeats 6400000 in

theorem KummerDatum.exists_antipode (hn : n ≠ 0) :
    ∃ S : D.Carrier →ₗ[O] D.Carrier,
      (LinearMap.mul' O (D.Carrier) ∘ₗ S.rTensor (D.Carrier) ∘ₗ (D.Δ).toLinearMap
        = Algebra.linearMap O (D.Carrier) ∘ₗ (D.ε).toLinearMap) ∧
      (LinearMap.mul' O (D.Carrier) ∘ₗ S.lTensor (D.Carrier) ∘ₗ (D.Δ).toLinearMap
        = Algebra.linearMap O (D.Carrier) ∘ₗ (D.ε).toLinearMap) := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)

  have hcu : ∀ k : Λ, IsUnit (D.c (-k) k * D.u k) := fun k => (D.isUnit_c hn (-k) k).mul (D.isUnit_u k)
  let s : Λ → O := fun k => ((hcu k).unit⁻¹ : Oˣ)
  have hkey : ∀ k : Λ, D.c (-k) k * (s k * D.u k) = 1 := by
    intro k
    rw [mul_left_comm, ← (hcu k).unit_spec]
    exact Units.inv_mul _
  have hsu : ∀ k : Λ, s k ^ n * D.u k ^ (n - 1) = D.u (-k) := by
    intro k
    have h1 : D.c (-k) k ^ n * (D.u (-k) * D.u k) = 1 := by rw [D.c_pow_mul, neg_add_cancel, D.u_zero]
    have h2 : (D.c (-k) k * (s k * D.u k)) ^ n = 1 := by rw [hkey, one_pow]
    calc s k ^ n * D.u k ^ (n - 1)
        = s k ^ n * D.u k ^ (n - 1) * (D.c (-k) k ^ n * (D.u (-k) * D.u k)) := by rw [h1, mul_one]
      _ = (D.c (-k) k * (s k * D.u k)) ^ n * D.u (-k) := by
          have hu : D.u k ^ n = D.u k ^ (n - 1) * D.u k := by rw [← pow_succ, hn1]
          rw [mul_pow, mul_pow, hu]; ring
      _ = D.u (-k) := by rw [h2, one_mul]
  have hσobl : ∀ k : Λ, (s k • D.z k ^ (n-1)) ^ n
      = algebraMap O (D.A k) (D.u (-k)) := by
    intro k
    rw [_root_.smul_pow, ← pow_mul, Nat.mul_comm (n-1) n, pow_mul, KummerDatum.z_pow,
      ← map_pow, Algebra.smul_def, ← map_mul, hsu]
  let σ : ∀ k : Λ, D.A (-k) →ₐ[O] D.A k := fun k =>
    AdjoinRoot.liftAlgHom (D.kpoly (-k)) (Algebra.ofId O (D.A k))
      (s k • D.z k ^ (n-1))
      (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
          exact (hσobl k).trans rfl)
  have hσ_root : ∀ k, σ k (D.z (-k)) = s k • D.z k ^ (n-1) := fun k => by
    show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
    rw [show AdjoinRoot.root (D.kpoly (-k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  let S : D.Carrier →ₐ[O] D.Carrier :=
    Pi.algHom _ _ fun k => (σ k).comp (Pi.evalAlgHom O D.A (-k))
  have hS_apply : ∀ (h : D.Carrier) (k : Λ), S h k = σ k (h (-k)) := fun _ _ => rfl
  have hcfac_symm : ∀ k : Λ, D.c (-k) k = D.c k (-k) := fun k => D.c_comm (-k) k
  have hΔ_comp : ∀ (h : D.Carrier) (a b : Λ),
      D.piPiEquiv (D.Δ h) a b = D.μ a b h := fun h a b => by
    have hrfl : D.Δ h = (D.piPiEquiv).symm
        ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => D.μ a b) h) := rfl
    rw [hrfl, AlgEquiv.apply_symm_apply]; rfl
  have hSr_comp : ∀ (y : D.Carrier ⊗[O] D.Carrier) (a b : Λ),
      D.piPiEquiv (Algebra.TensorProduct.map S (AlgHom.id O (D.Carrier)) y) a b
        = Algebra.TensorProduct.map (σ a) (AlgHom.id O (D.A b)) (D.piPiEquiv y (-a) b) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, D.piPiEquiv_tmul, hS_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hSl_comp : ∀ (y : D.Carrier ⊗[O] D.Carrier) (a b : Λ),
      D.piPiEquiv (Algebra.TensorProduct.map (AlgHom.id O (D.Carrier)) S y) a b
        = Algebra.TensorProduct.map (AlgHom.id O (D.A a)) (σ b) (D.piPiEquiv y a (-b)) := by
    intro y a b
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, D.piPiEquiv_tmul, hS_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hmul'_comp : ∀ (y : D.Carrier ⊗[O] D.Carrier) (k : Λ),
      Algebra.TensorProduct.lmul' O y k
        = Algebra.TensorProduct.lmul' O (D.piPiEquiv y k k) := by
    intro y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.lmul'_apply_tmul, D.piPiEquiv_tmul, Pi.mul_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

  have hnkval : ∀ k : Λ, (0 : Λ) = -k + k := fun k => (neg_add_cancel k).symm

  have hε_at_j : ∀ (j : Λ) (hj : (0 : Λ) = j) (h : D.Carrier),
      D.ε h = AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId O O) 1
        (by subst hj; simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X]) (h j) := by
    intro j hj h
    subst hj
    rfl
  have hnkval' : ∀ k : Λ, (0 : Λ) = k + -k := fun k => (add_neg_cancel k).symm
  have hpercomp_r : ∀ k : Λ,
      (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map (σ k) (AlgHom.id O (D.A k))).comp (D.μ (-k) k))
      = (Algebra.ofId O (D.A k)).comp (D.ε) := by
    intro k
    let εlift' : D.A (-k+k) →ₐ[O] O :=
      AdjoinRoot.liftAlgHom (D.kpoly (-k+k)) (Algebra.ofId O O) 1
        (by rw [← hnkval k]; simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X])
    let μlift : D.A (-k+k) →ₐ[O] D.A (-k) ⊗[O] D.A k :=
      AdjoinRoot.liftAlgHom (D.kpoly (-k+k)) (Algebra.ofId _ _)
        (D.c (-k) k • (D.z (-k) ⊗ₜ D.z k))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A (-k)),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A k),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have hμ_apply : ∀ h, D.μ (-k) k h = μlift (h (-k+k)) := fun _ => rfl
    have hGR : (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map (σ k) (AlgHom.id O (D.A k))).comp μlift)
      = (Algebra.ofId O (D.A k)).comp εlift' := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      have hμlift_root : μlift (AdjoinRoot.root (D.kpoly (-k+k)))
          = D.c (-k) k • (D.z (-k) ⊗ₜ D.z k) := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (D.kpoly (-k+k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      have hεlift'_root : εlift' (AdjoinRoot.root (D.kpoly (-k+k))) = 1 := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (D.kpoly (-k+k)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hσ_root, AlgHom.id_apply,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, smul_mul_assoc, ← pow_succ,
        hn1, KummerDatum.z_pow, Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul,
        mul_assoc, hkey, one_smul, hεlift'_root, map_one]
    apply AlgHom.ext; intro h
    simp only [AlgHom.comp_apply, Algebra.ofId_apply]
    rw [hμ_apply, hε_at_j (-k+k) (hnkval k) h]
    exact DFunLike.congr_fun hGR (h (-k+k))
  have hpercomp_l : ∀ k : Λ,
      (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map (AlgHom.id O (D.A k)) (σ k)).comp (D.μ k (-k)))
      = (Algebra.ofId O (D.A k)).comp (D.ε) := by
    intro k
    let εlift' : D.A (k+(-k)) →ₐ[O] O :=
      AdjoinRoot.liftAlgHom (D.kpoly (k+(-k))) (Algebra.ofId O O) 1
        (by rw [← hnkval' k]; simp [D.u_zero, eval₂_sub, eval₂_pow, eval₂_X])
    let μlift : D.A (k+(-k)) →ₐ[O] D.A k ⊗[O] D.A (-k) :=
      AdjoinRoot.liftAlgHom (D.kpoly (k+(-k))) (Algebra.ofId _ _)
        (D.c k (-k) • (D.z k ⊗ₜ D.z (-k)))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
              _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
            rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A k),
              Algebra.algebraMap_eq_smul_one (R := O) (A := D.A (-k)),
              TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
              ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
            rfl)
    have hμ_apply : ∀ h, D.μ k (-k) h = μlift (h (k+(-k))) := fun _ => rfl
    have hGR : (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map (AlgHom.id O (D.A k)) (σ k)).comp μlift)
      = (Algebra.ofId O (D.A k)).comp εlift' := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      have hμlift_root : μlift (AdjoinRoot.root (D.kpoly (k+(-k))))
          = D.c k (-k) • (D.z k ⊗ₜ D.z (-k)) := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (D.kpoly (k+(-k))) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      have hεlift'_root : εlift' (AdjoinRoot.root (D.kpoly (k+(-k)))) = 1 := by
        show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = _
        rw [show AdjoinRoot.root (D.kpoly (k+(-k))) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
          AdjoinRoot.liftAlgHom_mk, eval₂_X]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hσ_root, AlgHom.id_apply,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, mul_smul_comm, ← pow_succ',
        hn1, KummerDatum.z_pow, Algebra.algebraMap_eq_smul_one, smul_smul, smul_smul,
        ← hcfac_symm, mul_assoc, hkey, one_smul, hεlift'_root, map_one]
    apply AlgHom.ext; intro h
    simp only [AlgHom.comp_apply, Algebra.ofId_apply]
    rw [hμ_apply, hε_at_j (k+(-k)) (hnkval' k) h]
    exact DFunLike.congr_fun hGR (h (k+(-k)))
  refine ⟨S.toLinearMap, ?_, ?_⟩
  ·
    apply LinearMap.ext; intro h
    show LinearMap.mul' O _ (S.toLinearMap.rTensor _ (D.Δ h)) = algebraMap O _ (D.ε h)
    have hrT : S.toLinearMap.rTensor (D.Carrier) (D.Δ h)
        = Algebra.TensorProduct.map S (AlgHom.id O (D.Carrier)) (D.Δ h) := rfl
    have hmul : LinearMap.mul' O (D.Carrier)
        = (Algebra.TensorProduct.lmul' O (S := D.Carrier)).toLinearMap := rfl
    rw [hrT, hmul, AlgHom.toLinearMap_apply]
    funext k
    rw [hmul'_comp, hSr_comp, hΔ_comp, Pi.algebraMap_apply]
    exact DFunLike.congr_fun (hpercomp_r k) h
  ·
    apply LinearMap.ext; intro h
    show LinearMap.mul' O _ (S.toLinearMap.lTensor _ (D.Δ h)) = algebraMap O _ (D.ε h)
    have hlT : S.toLinearMap.lTensor (D.Carrier) (D.Δ h)
        = Algebra.TensorProduct.map (AlgHom.id O (D.Carrier)) S (D.Δ h) := rfl
    have hmul : LinearMap.mul' O (D.Carrier)
        = (Algebra.TensorProduct.lmul' O (S := D.Carrier)).toLinearMap := rfl
    rw [hlT, hmul, AlgHom.toLinearMap_apply]
    funext k
    rw [hmul'_comp, hSl_comp, hΔ_comp, Pi.algebraMap_apply]
    exact DFunLike.congr_fun (hpercomp_l k) h

end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_rTensor_comul mul_antipode_lTensor_comul"
p2m_open "HopfAlgebra"

open scoped TensorProduct
open Polynomial

universe u v
variable {O : Type u} [CommRing O] {n : ℕ} {Λ : Type u} [AddCommGroup Λ] [Fintype Λ] [DecidableEq Λ]
  (D : KummerDatum O n Λ)

set_option maxHeartbeats 3200000 in

theorem KummerDatum.evalAt_bijective_convHom [NeZero n]
    {L : Type u} [CommRing L] [IsDomain L] [Algebra O L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ n)
    (η : Λ → L) (hη : ∀ l, η l ^ n = algebraMap O L (D.u l))
    (hηmul : ∀ l l', η (l + l') = algebraMap O L (D.c l l') * η l * η l') :
    ∃ ψ₀ : ZMod n × Λ → (D.Carrier →ₐ[O] L),
      Function.Bijective ψ₀ ∧
      (∀ (i : ZMod n) (l : Λ), ∃ hw, ψ₀ (i, l) = D.evalAt l (ζ ^ i.val * η l) hw) ∧
      ∀ a b : ZMod n × Λ,
        (Algebra.TensorProduct.lmul' O (S := L)).comp
          ((Algebra.TensorProduct.map (ψ₀ a) (ψ₀ b)).comp D.Δ)
          = ψ₀ (a + b) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  have hη_ne : ∀ l, η l ≠ 0 := fun l h => by
    have hu : IsUnit (algebraMap O L (D.u l)) := (D.isUnit_u l).map _
    rw [← hη l, h, zero_pow (NeZero.ne n)] at hu
    exact not_isUnit_zero hu
  have hζwrap : ∀ a b : ZMod n, ζ ^ (a.val + b.val) = ζ ^ (a + b).val := by
    intro a b
    conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) n, pow_add, pow_mul, hζn, one_pow,
      mul_one, ← ZMod.val_add]
  have hw : ∀ (i : ZMod n) (l : Λ),
      (ζ ^ i.val * η l) ^ n = algebraMap O L (D.u l) := by
    intro i l
    rw [mul_pow, ← pow_mul, mul_comm i.val n, pow_mul, hζn, one_pow, one_mul, hη]
  have hkey : ∀ (i₁ : ZMod n) (l₁ : Λ) (i₂ : ZMod n) (l₂ : Λ),
      algebraMap O L (D.c l₁ l₂) * (ζ^i₁.val * η l₁) * (ζ^i₂.val * η l₂)
        = ζ^(i₁+i₂).val * η (l₁ + l₂) := by
    intro i₁ l₁ i₂ l₂
    calc _ = ζ^(i₁.val+i₂.val) * (algebraMap O L (D.c l₁ l₂) * η l₁ * η l₂) := by
            rw [pow_add]; ring
      _ = ζ^(i₁+i₂).val * η (l₁ + l₂) := by rw [hζwrap, hηmul]
  have hmap_eval : ∀ (a b : Λ) (y : D.Carrier ⊗[O] D.Carrier),
      Algebra.TensorProduct.map (Pi.evalAlgHom O D.A a) (Pi.evalAlgHom O D.A b) y
        = D.piPiEquiv y a b := by
    intro a b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul f g => simp [Algebra.TensorProduct.map_tmul, D.piPiEquiv_tmul]
    | add x y hx hy => simp only [map_add, hx, hy, Pi.add_apply]
  have hlift_root : ∀ (j : Λ) (w : L) (hwj),
      AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId O (L)) w hwj
        (AdjoinRoot.root (D.kpoly j)) = w := by
    intro j w hwj
    rw [show AdjoinRoot.root (D.kpoly j) = (AdjoinRoot.mk _) X from (AdjoinRoot.mk_X).symm,
      AdjoinRoot.liftAlgHom_mk, eval₂_X]
  have hevalAt_apply : ∀ (j : Λ) (w : L) (hwj) (h : D.Carrier),
      D.evalAt j w hwj h
        = AdjoinRoot.liftAlgHom (D.kpoly j) (Algebra.ofId O _) w
            (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
                exact hwj.trans rfl) (h j) := fun _ _ _ _ => rfl
  refine ⟨fun ⟨i, j⟩ => D.evalAt j (ζ ^ i.val * η j) (hw i j), ?_, ?_, ?_⟩

  · constructor

    · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
      have hprobe := DFunLike.congr_fun heq (Pi.single j₁ 1)
      rw [hevalAt_apply, hevalAt_apply] at hprobe
      have hj : j₁ = j₂ := by
        by_contra hne
        simp only [Pi.single_eq_same, map_one,
          Pi.single_eq_of_ne (Ne.symm hne), map_zero] at hprobe
        exact one_ne_zero hprobe
      subst hj
      have hprobe2 := DFunLike.congr_fun heq (Pi.single j₁ (D.z j₁))
      rw [hevalAt_apply, hevalAt_apply, Pi.single_eq_same, hlift_root, hlift_root] at hprobe2
      have hi : ζ ^ i₁.val = ζ ^ i₂.val :=
        mul_right_cancel₀ (hη_ne j₁) hprobe2
      exact Prod.ext (ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt i₁) (ZMod.val_lt i₂) hi)) rfl

    · intro φ
      have h1dec : (1 : D.Carrier) = ∑ k : Λ, (Pi.single k 1 : D.Carrier) := by
        funext l; simp [Finset.sum_apply, Finset.sum_pi_single]
      obtain ⟨j, hjne⟩ : ∃ j : Λ, φ (Pi.single j 1) ≠ 0 := by
        by_contra hall; push_neg at hall
        have h10 : (1 : L) = 0 := by
          rw [← map_one φ, h1dec, map_sum]
          exact Finset.sum_eq_zero fun k _ => hall k
        exact one_ne_zero h10
      have hj1 : φ (Pi.single j 1) = 1 := by
        have hidem : (Pi.single j 1 : D.Carrier) * Pi.single j 1 = Pi.single j 1 := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl]
        have h2 : φ (Pi.single j 1) * (φ (Pi.single j 1) - 1) = 0 := by
          have := congrArg φ hidem; rw [map_mul] at this; linear_combination this
        exact (mul_eq_zero.mp h2).elim (fun h => absurd h hjne) sub_eq_zero.mp
      have hk0 : ∀ k, k ≠ j → φ (Pi.single k 1) = 0 := fun k hk => by
        have hperp : (Pi.single j 1 : D.Carrier) * Pi.single k 1 = 0 := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp [Pi.single_eq_of_ne (Ne.symm hk)]
          · simp [Pi.single_eq_of_ne hl]
        have := congrArg φ hperp; rwa [map_mul, hj1, one_mul, map_zero] at this
      have hfactor : ∀ h : D.Carrier, φ h = φ (Pi.single j (h j)) := by
        intro h
        have hdec : h = ∑ k : Λ, Pi.single k (h k) := by
          funext l; simp [Finset.sum_apply, Finset.sum_pi_single]
        conv_lhs => rw [hdec, map_sum]
        refine Finset.sum_eq_single j (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ j) h)
        have : (Pi.single k (h k) : D.Carrier) = Pi.single k 1 * Pi.mulSingle k (h k) := by
          funext l
          rcases eq_or_ne l k with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
        rw [this, map_mul, hk0 k hk, zero_mul]
      have hmulSingle_eq : ∀ y : D.A j, φ (Pi.mulSingle j y) = φ (Pi.single j y) := by
        intro y
        have heq : (Pi.mulSingle j y : D.Carrier) = Pi.single j y + (1 - Pi.single j 1) := by
          funext l
          rcases eq_or_ne l j with rfl | hl
          · simp
          · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
        rw [heq, map_add, map_sub, map_one, hj1]; ring
      let φ₀ : D.A j →ₐ[O] L := AlgHom.ofLinearMap
        (φ.toLinearMap ∘ₗ LinearMap.single O (fun k => D.A k) j)
        (by simp only [LinearMap.comp_apply, LinearMap.coe_single, AlgHom.toLinearMap_apply];
            exact hj1)
        (fun x y => by
          simp only [LinearMap.comp_apply, LinearMap.coe_single, AlgHom.toLinearMap_apply]
          have : (Pi.single j (x * y) : D.Carrier) = Pi.single j x * Pi.mulSingle j y := by
            funext l
            rcases eq_or_ne l j with rfl | hl
            · simp
            · simp [Pi.single_eq_of_ne hl, Pi.mulSingle_eq_of_ne hl]
          rw [this, map_mul, hmulSingle_eq])
      have hφ₀_apply : ∀ x, φ₀ x = φ (Pi.single j x) := fun _ => rfl
      set w := φ₀ (D.z j) with hw_def
      have hwp : w ^ n = η j ^ n := by
        rw [hw_def, ← map_pow, KummerDatum.z_pow, AlgHom.commutes, hη]
      have hmem : w ∈ Polynomial.nthRoots n (η j ^ n) := (Polynomial.mem_nthRoots hn0).mpr hwp
      rw [hζ.nthRoots_eq (rfl : η j ^ n = η j ^ n)] at hmem
      obtain ⟨m, hm_mem, hm_eq⟩ := Multiset.mem_map.mp hmem
      have hmlt : m < n := Multiset.mem_range.mp hm_mem
      let i : ZMod n := (m : ZMod n)
      have hi_val : i.val = m := ZMod.val_natCast_of_lt hmlt
      have hi_eq : ζ ^ i.val * η j = w := by rw [hi_val]; exact hm_eq
      refine ⟨(i, j), AlgHom.ext fun h => ?_⟩
      rw [hevalAt_apply, hfactor h, ← hφ₀_apply]
      congr 1
      apply AdjoinRoot.algHom_ext
      rw [hlift_root, hi_eq, hw_def]

  · intro i j; exact ⟨hw i j, rfl⟩

  · rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    let lift₁ : D.A j₁ →ₐ[O] L :=
      AdjoinRoot.liftAlgHom (D.kpoly j₁) (Algebra.ofId O _) (ζ^i₁.val * η j₁)
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw i₁ j₁).trans rfl)
    let lift₂ : D.A j₂ →ₐ[O] L :=
      AdjoinRoot.liftAlgHom (D.kpoly j₂) (Algebra.ofId O _) (ζ^i₂.val * η j₂)
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw i₂ j₂).trans rfl)
    let μlift : D.A (j₁+j₂) →ₐ[O] D.A j₁ ⊗[O] D.A j₂ :=
      AdjoinRoot.liftAlgHom (D.kpoly (j₁+j₂)) (Algebra.ofId _ _)
        (D.c j₁ j₂ • (D.z j₁ ⊗ₜ D.z j₂))
        (by
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
            _root_.smul_pow, Algebra.TensorProduct.tmul_pow, KummerDatum.z_pow]
          rw [Algebra.algebraMap_eq_smul_one (R := O) (A := D.A j₁),
            Algebra.algebraMap_eq_smul_one (R := O) (A := D.A j₂),
            TensorProduct.smul_tmul_smul, smul_smul, D.c_pow_mul,
            ← Algebra.TensorProduct.one_def, ← Algebra.algebraMap_eq_smul_one]
          rfl)
    let rlift : D.A (j₁+j₂) →ₐ[O] L :=
      AdjoinRoot.liftAlgHom (D.kpoly (j₁+j₂)) (Algebra.ofId O _)
        (ζ^(i₁+i₂).val * η (j₁+j₂))
        (by simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero];
            exact (hw (i₁+i₂) (j₁+j₂)).trans rfl)
    have hlift₁_root : lift₁ (D.z j₁) = ζ^i₁.val * η j₁ := hlift_root _ _ _
    have hlift₂_root : lift₂ (D.z j₂) = ζ^i₂.val * η j₂ := hlift_root _ _ _
    have hμlift_root : μlift (AdjoinRoot.root (D.kpoly (j₁+j₂)))
        = D.c j₁ j₂ • (D.z j₁ ⊗ₜ D.z j₂) := by
      show AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root (D.kpoly (j₁+j₂))) = _
      rw [show AdjoinRoot.root (D.kpoly (j₁+j₂)) = AdjoinRoot.mk _ X from (AdjoinRoot.mk_X).symm,
        AdjoinRoot.liftAlgHom_mk, eval₂_X]
    have hrlift_root : rlift (AdjoinRoot.root (D.kpoly (j₁+j₂)))
        = ζ^(i₁+i₂).val * η (j₁+j₂) := hlift_root _ _ _
    have key : (Algebra.TensorProduct.lmul' O).comp
        ((Algebra.TensorProduct.map lift₁ lift₂).comp μlift) = rlift := by
      apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      rw [hμlift_root, map_smul, Algebra.TensorProduct.map_tmul, hlift₁_root, hlift₂_root,
        map_smul, Algebra.TensorProduct.lmul'_apply_tmul, hrlift_root, Algebra.smul_def,
        ← mul_assoc]
      exact hkey i₁ j₁ i₂ j₂
    have he1 : D.evalAt j₁ (ζ^i₁.val * η j₁) (hw i₁ j₁)
        = lift₁.comp (Pi.evalAlgHom O D.A j₁) := rfl
    have he2 : D.evalAt j₂ (ζ^i₂.val * η j₂) (hw i₂ j₂)
        = lift₂.comp (Pi.evalAlgHom O D.A j₂) := rfl
    have he12 : D.evalAt (j₁+j₂) (ζ^(i₁+i₂).val * η (j₁+j₂)) (hw (i₁+i₂) (j₁+j₂))
        = rlift.comp (Pi.evalAlgHom O D.A (j₁+j₂)) := rfl
    ext h
    simp only [AlgHom.comp_apply, Prod.fst_add, Prod.snd_add]
    have hΔh : D.piPiEquiv (D.Δ h) j₁ j₂ = D.μ j₁ j₂ h := by
      have hrfl : D.Δ h = (D.piPiEquiv).symm
          ((Pi.algHom _ _ fun a => Pi.algHom _ _ fun b => D.μ a b) h) := rfl
      rw [hrfl, AlgEquiv.apply_symm_apply]; rfl
    have hμ : D.μ j₁ j₂ h = μlift (h (j₁+j₂)) := rfl
    rw [he1, he2, Algebra.TensorProduct.map_comp, AlgHom.comp_apply, hmap_eval, hΔh, hμ, he12,
      AlgHom.comp_apply, Pi.evalAlgHom_apply]
    exact DFunLike.congr_fun key (h (j₁+j₂))

end HopfAlgebra

open _root_.HopfAlgebra _root_.P2MW.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle.HopfAlgebra in
set_option maxHeartbeats 6400000 in
theorem solution
    (O : Type) [CommRing O] [Nontrivial O] (p N : ℕ) [Fact p.Prime]
    (Λ : Type) [AddCommGroup Λ] [Finite Λ]
    (u : Λ → O) (hu : ∀ l : Λ, IsUnit (u l)) (hu0 : u 0 = 1)
    (c : Λ → Λ → O)
    (hc : ∀ l l' : Λ, c l l' ^ (p ^ N) * (u l * u l') = u (l + l'))
    (hc0 : ∀ l : Λ, c 0 l = 1) (hcomm : ∀ l l' : Λ, c l l' = c l' l)
    (hassoc : ∀ l l' l'' : Λ, c l l' * c (l + l') l'' = c l (l' + l'') * c l' l'') :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra O H),
      Module.Finite O H ∧ Module.Free O H ∧ Coalgebra.IsCocomm O H ∧
      Module.finrank O H = p ^ N * Nat.card Λ ∧
      ∀ (L : Type) [CommRing L] [IsDomain L] [Algebra O L] (ζ : L), IsPrimitiveRoot ζ (p ^ N) →
        ∀ η : Λ → L, (∀ l, η l ^ (p ^ N) = algebraMap O L (u l)) → η 0 = 1 →
          (∀ l l', η (l + l') = algebraMap O L (c l l') * η l * η l') →
          ∃ ψ : ZMod (p ^ N) × Λ ≃ WithConv (H →ₐ[O] L),
            (∀ a b, ψ (a + b) = ψ a * ψ b) ∧
            ∀ (τ : L →ₐ[O] L) (e : ℕ) (κ : Λ → ℕ), τ ζ = ζ ^ e → (∀ l, τ (η l) = ζ ^ κ l * η l) →
              ∀ (i : ZMod (p ^ N)) (l : Λ) (h : H), ψ (e • i + (κ l : ZMod (p ^ N)), l) h = τ (ψ (i, l) h) := by
  classical
  letI : Fintype Λ := Fintype.ofFinite Λ
  haveI hne : NeZero (p ^ N) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hn0 : p ^ N ≠ 0 := NeZero.ne _
  let D : HopfAlgebra.KummerDatum O (p ^ N) Λ :=
    { u := u, c := c, isUnit_u := hu, u_zero := hu0, c_pow_mul := hc, c_zero_left := hc0,
      c_comm := hcomm, c_assoc := hassoc }

  obtain ⟨hcoassoc, hrT, hlT, hcocomm⟩ := D.bialgebra_axioms
  letI bialg : Bialgebra O D.Carrier := Bialgebra.ofAlgHom D.Δ D.ε hcoassoc hrT hlT
  obtain ⟨S', hSr, hSl⟩ := D.exists_antipode hn0
  letI hopf : HopfAlgebra O D.Carrier :=
    { antipode := S'
      mul_antipode_rTensor_comul := hSr
      mul_antipode_lTensor_comul := hSl }
  haveI hCoc : Coalgebra.IsCocomm O D.Carrier := ⟨LinearMap.ext fun h => hcocomm h⟩

  haveI : ∀ l : Λ, Module.Free O (D.A l) := fun l => D.free_A hn0 l
  haveI : ∀ l : Λ, Module.Finite O (D.A l) := fun l => D.finite_A hn0 l
  have hrankA : ∀ l : Λ, Module.finrank O (D.A l) = p ^ N := fun l => by
    rw [(AdjoinRoot.powerBasis' (D.kpoly_monic hn0 l)).finrank, AdjoinRoot.powerBasis'_dim]
    exact Polynomial.natDegree_X_pow_sub_C
  have hrank : Module.finrank O D.Carrier = p ^ N * Nat.card Λ := by
    rw [Module.finrank_pi_fintype, Finset.sum_congr rfl (fun l _ => hrankA l), Finset.sum_const,
      smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
    rfl
  refine ⟨D.Carrier, inferInstance, hopf, inferInstance, inferInstance, hCoc, hrank, ?_⟩

  intro L _ _ _ ζ hζ η hη hη0 hηmul
  obtain ⟨ψ₀, hψbij, hψeval, hψΔ⟩ := D.evalAt_bijective_convHom ζ hζ η hη hηmul
  let ψ : ZMod (p ^ N) × Λ ≃ WithConv (D.Carrier →ₐ[O] L) :=
    (Equiv.ofBijective ψ₀ hψbij).trans (WithConv.equiv _).symm
  have hψof : ∀ x, (ψ x).ofConv = ψ₀ x := fun _ => rfl
  refine ⟨ψ, ?_, ?_⟩
  ·
    intro a b
    apply WithConv.ext
    rw [hψof, AlgHom.convMul_def, WithConv.ofConv_toConv, hψof, hψof]
    have hΔeq : Bialgebra.comulAlgHom O D.Carrier = D.Δ := AlgHom.ext fun _ => rfl
    rw [hΔeq]
    exact (hψΔ a b).symm
  ·
    intro τ e κ hτζ hτη i l h
    obtain ⟨hw1, heq1⟩ := hψeval (e • i + (κ l : ZMod (p ^ N))) l
    obtain ⟨hw2, heq2⟩ := hψeval i l
    obtain ⟨q, hq⟩ := D.exists_polyLift h l
    show (ψ _).ofConv h = τ ((ψ _).ofConv h)
    rw [hψof, hψof, heq1, heq2, D.evalAt_apply_z' _ _ _ h q hq, D.evalAt_apply_z' _ _ _ h q hq,
      ← Polynomial.aeval_algHom_apply τ]
    congr 1
    rw [map_mul, map_pow, hτζ, hτη, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
    have hmod : (e • i + (κ l : ZMod (p ^ N))) = ((e * i.val + κ l : ℕ) : ZMod (p ^ N)) := by
      push_cast
      simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    rw [hmod, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div (e * i.val + κ l) (p ^ N), pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, mul_one]

end S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle
end P2MW
export P2MW.S_HopfAlgebra_exists_kummerCarrier_withConv_equiv_of_kummerCocycle (solution)
