-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.FormalOK_bridge_net0O
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:04:43.009789+00:00
-- url     : https://prove2.me/submissions/2e153cd5-677f-4307-853c-c57203a27803

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Theorems.Thm_IntMul_Kappa_R6_Bit_formal_labels
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

open Matrix
open AModel (swapMat)
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

private theorem lmulF_one_apply {R : Type*} [CommRing R] {U : Type*} {m N : ℕ}
    (f : FV R U m N) :
    lmulF (R := R) (U := U) (1 : FMat m N) f = f := by
  change (Finsupp.lmapDomain R R (fun p : FMat m N × U => ((1 : FMat m N) * p.1, p.2)) : _ →ₗ[_] _) f = f
  have hmap : (fun p : FMat m N × U => ((1 : FMat m N) * p.1, p.2)) = id := by
    funext p; simp [one_mul]
  rw [hmap, Finsupp.lmapDomain_id]
  rfl

private theorem lmulF_swap_single {N : ℕ} (w : Fin 104719230) :
    lmulF (R := ZMod 2) (U := Fin 104719230) swapMat
      (Finsupp.single ((1 : FMat 529 N), w) (1 : ZMod 2)) =
    Finsupp.single (swapMat, w) (1 : ZMod 2) := by
  simp [lmulF, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, mul_one]

theorem solution (N : ℕ)
    (hG : LabGates N net0O.prog (fun _ => (1 : FMat 529 N)))
    (hLab : ∀ w, net0O.prog.foldl (labStepH N) (fun _ => (1 : FMat 529 N)) (.inl (net0O.ρ w)) =
      swapMat)
    (hSc : ∀ w, net0O.prog.foldl (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w)) =
      Finsupp.single ((1 : FMat 529 N), w) 1) :
    FormalOK (m := 529) net0O N := by
  intro w
  have hfl :=
    formal_labels (R := ZMod 2) (m := 529) (Wr := Fin 104719230 ⊕ Fin 3217907)
      (U := Fin 104719230) N net0O.prog (fun _ => (1 : FMat 529 N)) (fInit N) hG
  have hinit :
      (fun wr : Fin 104719230 ⊕ Fin 3217907 =>
        lmulF (R := ZMod 2) (U := Fin 104719230) (1 : FMat 529 N) (fInit N wr)) =
      fInit (R := ZMod 2) (m := 529) N :=
    funext fun wr => lmulF_one_apply (fInit N wr)
  have hrun :
      net0O.prog.foldl (fStep N) (fInit N) (.inl (net0O.ρ w)) =
        lmulF (net0O.prog.foldl (labStepH N) (fun _ => (1 : FMat 529 N)) (.inl (net0O.ρ w)))
          (net0O.prog.foldl (scalarStepM (R := ZMod 2)
            (M := FV (ZMod 2) (Fin 104719230) 529 N)) (fInit N) (.inl (net0O.ρ w))) := by
    have := congrArg (fun F => F (.inl (net0O.ρ w))) hfl
    simpa [hinit] using this
  rw [hrun, hLab w, hSc w]
  exact lmulF_swap_single (N := N) w
