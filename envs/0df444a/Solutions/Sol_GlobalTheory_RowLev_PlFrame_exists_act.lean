-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.exists_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:47:00.559673+00:00
-- url     : https://prove2.me/submissions/3942d0b0-86d8-4aa4-8a20-82a512db0c20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_ActsAs_mul
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_actsAs_one
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_exists_actsAs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
namespace GlobalTheory.RowLev.PlFrame
theorem _root_.solution : ∃ ρ : I.Gf → GL (Fin N) (ZMod p),
    (∀ x ∈ I.Kset, fr.ActsAs x (ρ x : Matrix (Fin N) (Fin N) (ZMod p))) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ (x * x') = ρ x * ρ x' := by
  classical
  have h0 : ∀ x : Ksub I, ∃ M, fr.ActsAs x.1 M := fun x => fr.exists_actsAs (x := x.1) x.2
  choose M hM using h0
  have hmul : ∀ x y : Ksub I, M (x * y) = M x * M y := fun x y =>
    ActsAs.unique fr (x := x.1 * y.1) (x * y).2 (hM (x * y)) (ActsAs.mul fr (x := x.1) (x' := y.1) y.2 (hM x) (hM y))
  have hone : M 1 = 1 := ActsAs.unique fr (x := 1) (Ksub I).one_mem (hM 1) fr.actsAs_one
  obtain ⟨φ, hφ⟩ : ∃ φ : Ksub I →* GL (Fin N) (ZMod p), ∀ x, (φ x).val = M x :=
    ⟨(⟨⟨M, hone⟩, hmul⟩ : Ksub I →* Matrix (Fin N) (Fin N) (ZMod p)).toHomUnits, fun _ => rfl⟩
  refine ⟨fun x => if h : x ∈ Ksub I then φ ⟨x, h⟩ else 1, fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hx' : x ∈ Ksub I := hx
    beta_reduce
    rw [dif_pos hx', hφ]
    exact hM ⟨x, hx'⟩
  · have hx' : x ∈ Ksub I := hx
    have hy' : y ∈ Ksub I := hy
    beta_reduce
    rw [dif_pos hx', dif_pos hy', dif_pos (mul_mem hx' hy'), ← φ.map_mul]
    rfl
end GlobalTheory.RowLev.PlFrame
