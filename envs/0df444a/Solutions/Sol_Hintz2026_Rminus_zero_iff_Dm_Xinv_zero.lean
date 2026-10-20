-- Prove2me | solution 1 for Hintz2026.Rminus_zero_iff_Dm_Xinv_zero
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:59:05.442917+00:00
-- url     : https://prove2.me/submissions/ebf993f7-7f81-466f-9f90-108b631adfcb

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dm_Xv_sub_AXv
import Theorems.Thm_Hintz2026_Dm_congr
import Theorems.Thm_Hintz2026_contDiffOn_Xinv_mulVec

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (u : (Fin 2 → ℝ) → Fin 2 → ℂ) (hu : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => u x j) (U p)) {x : Fin 2 → ℝ} (hx : x ∈ U p) : (fun j => Dm p (fun z => ((X p z)⁻¹ *ᵥ u z) j) x) = 0 ↔ (fun i => Dm p (fun z => u z i) x) - A p x *ᵥ u x = 0 :=
  by
    set v : (Fin 2 → ℝ) → Fin 2 → ℂ := fun z => (X p z)⁻¹ *ᵥ u z
    have hvs : ∀ j, ContDiffOn ℝ ∞ (fun x => v x j) (U p) :=
      fun j => contDiffOn_Xinv_mulVec p hu j
    have hXv : ∀ z ∈ U p, X p z *ᵥ v z = u z := fun z hz => X_Xinv_mulVec p hz (u z)
    have hres := Dm_Xv_sub_AXv p hx v
      (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hvs hx j k)
    have key : (fun i => Dm p (fun z => u z i) x) - A p x *ᵥ u x =
        X p x *ᵥ (fun j => Dm p (fun z => v z j) x) := by
      conv_lhs => ext i; rw [Pi.sub_apply,
        ← show Dm p (fun z => (X p z *ᵥ v z) i) x = Dm p (fun z => u z i) x from
          Dm_congr p hx (fun z hz => congr_fun (hXv z hz) i),
        ← show (A p x *ᵥ (X p x *ᵥ v x)) i = (A p x *ᵥ u x) i from by rw [hXv x hx]]
      exact hres
    rw [key]; constructor
    · intro h; rw [h, mulVec_zero]
    · intro h
      have := congr_arg ((X p x)⁻¹ *ᵥ ·) h
      rwa [mulVec_mulVec, inv_mul_X p hx, one_mulVec, mulVec_zero] at this

end
