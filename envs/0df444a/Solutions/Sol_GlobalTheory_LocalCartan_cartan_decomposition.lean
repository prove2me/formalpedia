-- Prove2me | solution 1 for GlobalTheory.LocalCartan.cartan_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:44.730806+00:00
-- url     : https://prove2.me/submissions/91f97573-9aca-4705-b724-9ca112d96e7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Theorems.Thm_GlobalTheory_LocalCartan_diagT_mem_KO
import Theorems.Thm_GlobalTheory_LocalCartan_exists_diagT
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
namespace GlobalTheory.LocalCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_one_twisted_operators : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
  _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_inv_twisted_operators (y : kˣ) :
    _root_.GlobalTheory.SmGL.ord k y⁻¹ = -_root_.GlobalTheory.SmGL.ord k y := by
  have h := _root_.GlobalTheory.SmGL.ord_mul k y y⁻¹
  rw [mul_inv_cancel, ord_one_twisted_operators] at h
  omega
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma ord_zpow_uniformizer' {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
  have h1 := _root_.GlobalTheory.SmGL.ord_eq_one hϖ
  induction m using Int.induction_on with
  | zero => simpa using ord_one_twisted_operators
  | succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]
  | pred i ih =>
    rw [_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]
    ring
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] in
private lemma exists_unit_mul_zpow_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ x = u * ϖ ^ m := by
  refine ⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩
  apply _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp
  rw [_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators,
    ord_zpow_uniformizer' hϖ]
  ring
end GlobalTheory.LocalCartan
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open GlobalTheory GlobalTheory.LocalCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.LocalCartan
namespace _root_.GlobalTheory.LocalCartan
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    (ϖ : kˣ) (g : GL n k) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ m : n → ℤ, g = x * _root_.GlobalTheory.SmGL.diagT k n (fun i => ϖ ^ m i) * y := by
  obtain ⟨x, hx, y, hy, t, rfl⟩ := _root_.GlobalTheory.LocalCartan.exists_diagT g
  choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)
  refine ⟨x * _root_.GlobalTheory.SmGL.diagT k n u,
    mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩
  have ht : t = u * fun i => ϖ ^ m i := funext htu
  rw [ht, map_mul]
  simp only [mul_assoc]
end _root_.GlobalTheory.LocalCartan
end GlobalTheory.LocalCartan
