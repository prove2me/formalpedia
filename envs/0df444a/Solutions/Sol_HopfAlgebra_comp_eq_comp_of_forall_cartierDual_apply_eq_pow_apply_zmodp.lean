-- Prove2me | solution 1 for HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8fb702f2-0a76-5f62-a326-f1dd0fb03ebd

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp

set_option autoImplicit false

namespace Ws23
namespace VComm

theorem eq_zero_of_forall_cartierDual_apply_eq_zero (p : ℕ) [Fact p.Prime]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C]
    (c : C) (h : ∀ φ : CartierDual (ZMod p) C, φ c = 0) : c = 0 := by
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod p) c).1 fun f => h (CartierDual.ofDual (ZMod p) C f)

theorem main (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q := by
  apply BialgHom.ext
  intro b
  rw [BialgHom.comp_apply, BialgHom.comp_apply]
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_cartierDual_apply_eq_zero p
  intro φ
  rw [map_sub, sub_eq_zero]
  calc φ (q (VB b)) = CartierDual.map q φ (VB b) := (CartierDual.map_apply q φ (VB b)).symm
    _ = ((CartierDual.map q φ) ^ p) b := hVB _ b
    _ = (CartierDual.map q (φ ^ p)) b := by rw [map_pow]
    _ = (φ ^ p) (q b) := CartierDual.map_apply q (φ ^ p) b
    _ = φ (VC (q b)) := (hVC φ (q b)).symm

end Ws23.VComm

theorem solution
    (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q :=
  Ws23.VComm.main p q VB hVB VC hVC

end S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
end P2MW
export P2MW.S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp (solution)
