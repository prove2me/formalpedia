-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.scalarOK_module_lift_net0O
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:20:37.922322+00:00
-- url     : https://prove2.me/submissions/686771e1-4543-4615-92d2-3894494e4771

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open Matrix
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2

/-- Linear functionals intertwine `gateVecM` with `gateVec`. -/
private lemma gateVecM_apply_linear {R : Type*} [CommRing R] {Wr : Type*} [DecidableEq Wr]
    {M : Type*} [AddCommGroup M] [Module R M]
    (α : M →ₗ[R] R) (g : Matrix Wr Wr R) (S : Finset Wr) (v : Wr → M) (w : Wr) :
    α (gateVecM g S v w) = gateVec g S (fun w' => α (v w')) w := by
  simp only [gateVecM, gateVec]
  split_ifs with hw
  · simp only [map_sum, map_smul, smul_eq_mul]
  · rfl

/-- Linear functionals intertwine `foldl scalarStepM` with `foldl scalarStepH`. -/
private lemma foldl_scalarStepM_apply_linear {R : Type*} [CommRing R] {m : ℕ}
    {Wr : Type*} [Fintype Wr] [DecidableEq Wr]
    {M : Type*} [AddCommGroup M] [Module R M]
    (α : M →ₗ[R] R) :
    ∀ (prog : List (Instr Wr R m)) (v : Wr → M) (w : Wr),
      α (prog.foldl scalarStepM v w) = prog.foldl scalarStepH (fun w' => α (v w')) w := by
  intro prog
  induction prog with
  | nil => intro v w; rfl
  | cons i rest ih =>
    intro v w
    cases i with
    | gate g S =>
      -- One gate step, then the inductive hypothesis.
      have hstate :
          (fun w' => α (gateVecM (R := R) (M := M) g S v w')) =
            gateVec (R := R) g S (fun w' => α (v w')) := by
        funext w'
        exact gateVecM_apply_linear (R := R) (M := M) α g S v w'
      -- `scalarStepM v (.gate g S) = gateVecM g S v`
      -- `scalarStepH (α∘v) (.gate g S) = gateVec g S (α∘v)`
      change α (rest.foldl scalarStepM (gateVecM g S v) w) =
        rest.foldl scalarStepH (gateVec g S (fun w' => α (v w'))) w
      simpa [hstate] using ih (gateVecM g S v) w
    | edge w0 e =>
      -- Edges are identity on the scalar circuit.
      simpa [scalarStepM, scalarStepH] using ih v w

theorem solution (N : ℕ)
    (hS : ScalarOK (m := 529) (R := ZMod 2) net0O) (w : Fin 104719230) :
    net0O.prog.foldl (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w)) =
      Finsupp.single ((1 : FMat 529 N), w) 1 := by
  refine Finsupp.ext fun p => ?_
  let α : FV (ZMod 2) (Fin 104719230) 529 N →ₗ[ZMod 2] ZMod 2 := Finsupp.lapply p
  have hlin :=
    foldl_scalarStepM_apply_linear (R := ZMod 2) (m := 529)
      (Wr := Fin 104719230 ⊕ Fin 3217907)
      (M := FV (ZMod 2) (Fin 104719230) 529 N) α
      net0O.prog (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w))
  have hinit :
      (fun wr : Fin 104719230 ⊕ Fin 3217907 =>
        α (fInit (R := ZMod 2) (m := 529) N wr)) =
        Sum.elim (fun u => α (Finsupp.single ((1 : FMat 529 N), u) 1)) fun _ => (0 : ZMod 2) := by
    funext wr
    cases wr with
    | inl u => simp [fInit]
    | inr t => simp [fInit]
  have hsc := hS (fun u => α (Finsupp.single ((1 : FMat 529 N), u) 1)) w
  -- hlin : α (foldl scalarStepM fInit (inl ρ w)) = foldl scalarStepH (α∘fInit) (inl ρ w)
  -- rewrite α∘fInit via hinit, then apply ScalarOK
  have : α (net0O.prog.foldl
      (scalarStepM (R := ZMod 2) (M := FV (ZMod 2) (Fin 104719230) 529 N))
      (fInit (R := ZMod 2) (m := 529) N) (.inl (net0O.ρ w))) =
      α (Finsupp.single ((1 : FMat 529 N), w) 1) := by
    rw [hlin]
    -- foldl scalarStepH (α∘fInit) = foldl scalarStepH (Sum.elim ...)
    have hcongr :
        (fun wr => α (fInit (R := ZMod 2) (m := 529) N wr)) =
          Sum.elim (fun u => α (Finsupp.single ((1 : FMat 529 N), u) 1)) fun _ => 0 := hinit
    rw [hcongr, hsc]
  simpa [α, Finsupp.lapply_apply] using this
