-- Prove2me | solution 1 for Hintz2026.Rplus_zero_iff_Dp_Xstar_zero
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:59:07.282652+00:00
-- url     : https://prove2.me/submissions/6d7b3b89-fd12-4239-ad1d-980d7f703cb2

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dp_Yv_add_AYv
import Theorems.Thm_Hintz2026_Dp_congr
import Theorems.Thm_Hintz2026_contDiffOn_Xstar_mulVec

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (u : (Fin 2 → ℝ) → Fin 2 → ℂ) (hu : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => u x j) (U p)) {x : Fin 2 → ℝ} (hx : x ∈ U p) : (fun j => Dp p (fun z => ((X p z)ᴴ *ᵥ u z) j) x) = 0 ↔ (fun i => Dp p (fun z => u z i) x) + A p x *ᵥ u x = 0 :=
  by
    set v : (Fin 2 → ℝ) → Fin 2 → ℂ := fun z => (X p z)ᴴ *ᵥ u z
    have hvs : ∀ j, ContDiffOn ℝ ∞ (fun x => v x j) (U p) :=
      fun j => contDiffOn_Xstar_mulVec p hu j
    have hYv : ∀ z ∈ U p, ((X p z)ᴴ)⁻¹ *ᵥ v z = u z := fun z hz => Y_Xstar_mulVec p hz (u z)
    have hres := Dp_Yv_add_AYv p hx v
      (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hvs hx j k)
    have key : (fun i => Dp p (fun z => u z i) x) + A p x *ᵥ u x =
        ((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x) := by
      conv_lhs => ext i; rw [Pi.add_apply,
        ← show Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x = Dp p (fun z => u z i) x from
          Dp_congr p hx (fun z hz => congr_fun (hYv z hz) i),
        ← show (A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x)) i = (A p x *ᵥ u x) i from by rw [hYv x hx]]
      exact hres
    rw [key]; constructor
    · intro h; rw [h, mulVec_zero]
    · intro h
      have := congr_arg ((X p x)ᴴ *ᵥ ·) h
      rwa [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec, mulVec_zero] at this

end
