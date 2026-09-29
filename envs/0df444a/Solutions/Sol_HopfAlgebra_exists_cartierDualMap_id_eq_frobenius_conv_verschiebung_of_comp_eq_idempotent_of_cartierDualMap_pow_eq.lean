-- Prove2me | solution 1 for HopfAlgebra.exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9252cc72-a275-5be6-9dd7-fa6ce0996b18

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped TensorProduct

namespace IdInFV

theorem charP_of_nontrivial (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] [Nontrivial A] :
    CharP A p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

noncomputable def frobAlgHom (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] [Nontrivial A] :
    A →ₐ[ZMod p] A :=
  haveI := charP_of_nontrivial p A
  { frobenius A p with
    commutes' := fun r => by
      show (frobenius A p) (algebraMap (ZMod p) A r) = algebraMap (ZMod p) A r
      rw [frobenius_def, ← map_pow, ZMod.pow_card] }

theorem frobAlgHom_apply (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] [Nontrivial A] (x : A) :
    frobAlgHom p A x = x ^ p := rfl

theorem nontrivial_of_bialgebra (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod p) B] : Nontrivial B :=
  (Bialgebra.counitAlgHom (ZMod p) B : B →+* ZMod p).domain_nontrivial

theorem map_frob_frob_apply (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod p) B] [Nontrivial B]
    (z : B ⊗[ZMod p] B) :
    Algebra.TensorProduct.map (frobAlgHom p B) (frobAlgHom p B) z = z ^ p := by
  haveI : Nontrivial (B ⊗[ZMod p] B) :=
    (Algebra.TensorProduct.lmul' (ZMod p) (S := B)).toRingHom.domain_nontrivial
  haveI := charP_of_nontrivial p (B ⊗[ZMod p] B)
  induction z with
  | zero => rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  | tmul a b => rw [Algebra.TensorProduct.map_tmul, frobAlgHom_apply, frobAlgHom_apply, Algebra.TensorProduct.tmul_pow]
  | add x y hx hy => rw [map_add, hx, hy, add_pow_char]

noncomputable def frobBialgHom (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod p) B] [Nontrivial B] :
    B →ₐc[ZMod p] B :=
  BialgHom.ofAlgHom (frobAlgHom p B)
    (by
      apply AlgHom.ext; intro x
      rw [AlgHom.comp_apply, frobAlgHom_apply, map_pow, ZMod.pow_card])
    (by
      apply AlgHom.ext; intro x
      rw [AlgHom.comp_apply, AlgHom.comp_apply, map_frob_frob_apply, frobAlgHom_apply, map_pow])

theorem frobBialgHom_apply (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] [Bialgebra (ZMod p) B] [Nontrivial B] (x : B) :
    frobBialgHom p B x = x ^ p := rfl

section Iterates

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Bialgebra R B]

def itR (u : B →ₐc[R] B) : ℕ → (B →ₐc[R] B)
  | 0 => BialgHom.id R B
  | n + 1 => (itR u n).comp u

def itL (w : B →ₐc[R] B) : ℕ → (B →ₐc[R] B)
  | 0 => BialgHom.id R B
  | n + 1 => w.comp (itL w n)

theorem itR_zero (u : B →ₐc[R] B) : itR u 0 = BialgHom.id R B := rfl
theorem itR_succ (u : B →ₐc[R] B) (n : ℕ) : itR u (n + 1) = (itR u n).comp u := rfl
theorem itL_zero (w : B →ₐc[R] B) : itL w 0 = BialgHom.id R B := rfl
theorem itL_succ (w : B →ₐc[R] B) (n : ℕ) : itL w (n + 1) = w.comp (itL w n) := rfl

variable [Module.Finite R B] [Module.Free R B]

theorem map_pow_eq (u : B →ₐc[R] B) (n : ℕ) :
    (CartierDual.map u : CartierDual R B →ₗ[R] CartierDual R B) ^ n =
      (CartierDual.map (itR u n) : CartierDual R B →ₗ[R] CartierDual R B) := by
  induction n with
  | zero =>
    rw [pow_zero, itR_zero, CartierDual.map_id]
    rfl
  | succ n ih =>
    rw [pow_succ', ih, itR_succ, CartierDual.map_comp]
    rfl

theorem itL_comp_itR_comp_eq (u ε w : B →ₐc[R] B) (hεu : ε.comp u = u.comp ε) (hwuε : w.comp (u.comp ε) = ε) (n : ℕ) :
    (itL w n).comp ((itR u n).comp ε) = ε := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [itL_succ, itR_succ]
    calc (w.comp (itL w n)).comp (((itR u n).comp u).comp ε)
        = (w.comp (itL w n)).comp (((itR u n).comp ε).comp u) := by
          rw [BialgHom.comp_assoc (itR u n) u ε, ← hεu, ← BialgHom.comp_assoc (itR u n) ε u]
      _ = (w.comp ((itL w n).comp ((itR u n).comp ε))).comp u := by
          rw [← BialgHom.comp_assoc, BialgHom.comp_assoc w]
      _ = ε := by rw [ih, BialgHom.comp_assoc, hεu, hwuε]

end Iterates

end IdInFV

open IdInFV in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] [Module.Free (ZMod p) B]
    (u ε w : B →ₐc[ZMod p] B)
    (hεε : ε.comp ε = ε) (hεu : ε.comp u = u.comp ε)
    (hεw : ε.comp w = w) (hwε : w.comp ε = w)
    (hwuε : w.comp (u.comp ε) = ε) (huεw : (u.comp ε).comp w = ε)
    (hFV : ∀ Fk : B →ₐc[ZMod p] B, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B, (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (n : ℕ) (a b : CartierDual (ZMod p) B →ₐc[ZMod p] CartierDual (ZMod p) B),
        (CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ n =
          (WithConv.toConv ((FD : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
              (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) *
            WithConv.toConv ((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B))).ofConv)
    (C : Type) [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C]
    [Module.Finite (ZMod p) C] [Module.Free (ZMod p) C]
    (q : B →ₐc[ZMod p] C) (i : C →ₐc[ZMod p] B)
    (hq : Function.Surjective q) (hqi : q.comp i = BialgHom.id (ZMod p) C) (hiq : i.comp q = ε) :
    ∀ Fk : C →ₐc[ZMod p] C, (∀ x, Fk x = x ^ p) →
      ∀ FD : CartierDual (ZMod p) C →ₐ[ZMod p] CartierDual (ZMod p) C, (∀ ψ, FD ψ = ψ ^ p) →
      ∃ (a b : CartierDual (ZMod p) C →ₐc[ZMod p] CartierDual (ZMod p) C),
        (CartierDual.map (BialgHom.id (ZMod p) C) :
            CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) =
          (WithConv.toConv ((FD : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
              (a : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C)) *
            WithConv.toConv ((b : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
              (CartierDual.map Fk : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C))).ofConv := by
  intro FkC hFkC FDC hFDC
  classical

  haveI : Nontrivial B := nontrivial_of_bialgebra p B
  haveI : Nontrivial (CartierDual (ZMod p) B) := nontrivial_of_bialgebra p (CartierDual (ZMod p) B)
  let FkB : B →ₐc[ZMod p] B := frobBialgHom p B
  have hFkB : ∀ x, FkB x = x ^ p := fun x => rfl
  let FDB : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B := frobAlgHom p (CartierDual (ZMod p) B)
  have hFDB : ∀ ψ, FDB ψ = ψ ^ p := fun ψ => rfl
  obtain ⟨n, a, b, hab⟩ := hFV FkB hFkB FDB hFDB

  set G : CartierDual (ZMod p) B →ₐc[ZMod p] CartierDual (ZMod p) C := (CartierDual.map i).comp (CartierDual.map ε) with hG
  set Hh : CartierDual (ZMod p) C →ₐc[ZMod p] CartierDual (ZMod p) B := (CartierDual.map (itL w n)).comp (CartierDual.map q) with hHh

  have hqε : q = q.comp ε := by rw [← hiq, ← BialgHom.comp_assoc, hqi, BialgHom.id_comp]
  have hεpow : ε = (itL w n).comp ((itR u n).comp ε) := (itL_comp_itR_comp_eq u ε w hεu hwuε n).symm
  have h1 : (CartierDual.map (BialgHom.id (ZMod p) C) : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) =
      (G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
        ((CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ n) ∘ₗ
        (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B) := by
    have hb : CartierDual.map (BialgHom.id (ZMod p) C) = (G.comp (CartierDual.map (itR u n))).comp Hh := by
      rw [hG, hHh, ← hqi, CartierDual.map_comp]
      conv_lhs => rw [hqε, hεpow]
      rw [CartierDual.map_comp, CartierDual.map_comp, CartierDual.map_comp]
      simp only [BialgHom.comp_assoc]
    rw [hb, map_pow_eq]
    rfl

  have h2 : (G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
        ((CartierDual.map u : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ^ n) ∘ₗ
        (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B) =
      (WithConv.toConv ((G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
          ((FDB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
            (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) ∘ₗ
          (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B)) *
        WithConv.toConv ((G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
          ((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
            (CartierDual.map FkB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) ∘ₗ
          (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B))).ofConv := by
    rw [hab]
    have hH := @LinearMap.convMul_comp_coalgHom_distrib (ZMod p) (CartierDual (ZMod p) B)
      (CartierDual (ZMod p) C) (CartierDual (ZMod p) B) _ _ Algebra.toModule _ _ _ _ _ _ _ _
      (WithConv.toConv ((FDB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)))
      (WithConv.toConv ((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (CartierDual.map FkB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)))
      Hh.toCoalgHom
    have hGd := LinearMap.algHom_comp_convMul_distrib (G : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) C)
      (WithConv.toConv (((FDB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (a : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) ∘ₗ
        (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B)))
      (WithConv.toConv (((b : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (CartierDual.map FkB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B)) ∘ₗ
        (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B)))
    rw [LinearMap.comp_assoc]
    erw [hH]
    erw [hGd]
    rfl

  have h3a : (G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
        (FDB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) =
      (FDC : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) ∘ₗ
        (G : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) C) := by
    apply LinearMap.ext; intro ψ
    show G (FDB ψ) = FDC (G ψ)
    rw [hFDB, hFDC, map_pow]
  have hcommF : q.comp ((itL w n).comp FkB) = FkC.comp (q.comp (itL w n)) := by
    apply BialgHom.coe_algHom_injective
    apply AlgHom.ext; intro x
    show q ((itL w n) (FkB x)) = FkC (q ((itL w n) x))
    rw [hFkB, hFkC, map_pow, map_pow]
  have h3b : (CartierDual.map FkB : CartierDual (ZMod p) B →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B) =
      (Hh : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B) ∘ₗ
        (CartierDual.map FkC : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) C) := by
    have : (CartierDual.map FkB).comp Hh = Hh.comp (CartierDual.map FkC) := by
      rw [hHh, ← BialgHom.comp_assoc, ← CartierDual.map_comp, ← CartierDual.map_comp, hcommF, CartierDual.map_comp,
        CartierDual.map_comp, BialgHom.comp_assoc]
    exact congrArg (fun f : CartierDual (ZMod p) C →ₐc[ZMod p] CartierDual (ZMod p) B =>
      (f : CartierDual (ZMod p) C →ₗ[ZMod p] CartierDual (ZMod p) B)) this
  refine ⟨G.comp (a.comp Hh), G.comp (b.comp Hh), ?_⟩
  rw [h1, h2]
  congr 2
  ·
    refine congrArg WithConv.toConv ?_
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h3a, LinearMap.comp_assoc, LinearMap.comp_assoc]
    exact LinearMap.ext fun _ => rfl
  ·
    refine congrArg WithConv.toConv ?_
    rw [LinearMap.comp_assoc, h3b, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    exact LinearMap.ext fun _ => rfl

end S_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq
end P2MW
export P2MW.S_HopfAlgebra_exists_cartierDualMap_id_eq_frobenius_conv_verschiebung_of_comp_eq_idempotent_of_cartierDualMap_pow_eq (solution)
