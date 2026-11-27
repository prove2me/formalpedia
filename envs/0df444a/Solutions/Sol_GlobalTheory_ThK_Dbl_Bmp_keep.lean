-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Bmp.keep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:54.821738+00:00
-- url     : https://prove2.me/submissions/d91595cb-6c40-4a0a-997b-cb94849bf869

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
import Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_mem_lam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K]
namespace GlobalTheory.ThK.Dbl.Bmp
theorem _root_.solution {h : Matrix (Fin n) (Fin n) K} (hh : h - 1 ∈ lam K a n n) (y : Matrix (Fin n) (Fin d) O) {Y : Matrix (Fin n) (Fin d) K}
    (hY : Y - y.map (algebraMap O K) ∈ lam K a n d) : h * Y - y.map (algebraMap O K) ∈ lam K a n d := by
  rw [mem_lam] at hh hY ⊢
  obtain ⟨α, hα⟩ := hh
  obtain ⟨β, hβ⟩ := hY
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  refine ⟨β + α * y + a • (α * β), ?_⟩
  have e1 : h = 1 + a • α.map (algebraMap O K) := by rw [hα]; abel
  have e2 : Y = y.map (algebraMap O K) + a • β.map (algebraMap O K) := by rw [hβ]; abel
  rw [e1, e2, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_smul (algebraMap O K) a hf, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  abel
end GlobalTheory.ThK.Dbl.Bmp
