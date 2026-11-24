-- Prove2me | solution 1 for GlobalTheory.LocalCartan.exists_diagT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:05:13.563911+00:00
-- url     : https://prove2.me/submissions/c56cf26f-7139-4af8-b213-a238a814688b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Theorems.Thm_Formalism_UG_P_cartan_smith
import Theorems.Thm_GlobalTheory_SmGL_val_diagT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k])
    (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)
  choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))
  set f := algebraMap 𝒪[k] k with hf
  set c : k := f b with hc_def
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hG i j, Algebra.smul_def]
  have hdet : (Matrix.of G).det ≠ 0 := by
    intro h0
    have h1 := congrArg f h0
    rw [RingHom.map_det, hGg, map_zero, Matrix.det_smul] at h1
    exact mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1
  obtain ⟨P, C, hP, hC, a, ha, hPC⟩ := _root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hmap : ∀ A : GL n 𝒪[k],
      ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k]) :=
    fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl
  have hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n :=
    fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩
  have hne : ∀ i, f (a i) / c ≠ 0 := fun i =>
    div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc
  refine ⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC),
    fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩
  have key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k) := by
    have hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i)) := by
      rw [RingHom.mapMatrix_apply]
      exact Matrix.diagonal_map (map_zero f)
    rw [← hGg, hPC, map_mul, map_mul, hd]
  have hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) =
      c⁻¹ • diagonal (fun i => f (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]
  change (g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]
end _root_.GlobalTheory.LocalCartan
end GlobalTheory.LocalCartan
