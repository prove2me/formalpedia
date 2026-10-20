-- Prove2me | solution 1 for Hintz2026.system4_iff_system7
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:11:30.245521+00:00
-- url     : https://prove2.me/submissions/8289fb98-50b0-4620-be9b-caa92a68ad52

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_system7_zplus_of_system4
import Theorems.Thm_Hintz2026_system7_zminus_of_system4
import Theorems.Thm_Hintz2026_system4_yplus_of_system7
import Theorems.Thm_Hintz2026_system4_yminus_of_system7
import Theorems.Thm_Hintz2026_contDiffOn_Xstar_mulVec
import Theorems.Thm_Hintz2026_Dm_congr
import Theorems.Thm_Hintz2026_Dp_congr

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : ((fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x ∧ (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x) ↔ ((fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ ((X p x)ᴴ *ᵥ yminus x) ∧ (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ (adjugate (X p x) *ᵥ yplus x)) :=
  by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨system7_zplus_of_system4 p yplus yminus sg om mm hyp hym hx h1,
             system7_zminus_of_system4 p yplus yminus sg om mm hyp hym hx h2⟩
    · rintro ⟨h1, h2⟩
      -- apply the reverse direction to zp := adj(X) y+, zm := X^H y-, then undo the round trips
      have hzp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => (adjugate (X p x) *ᵥ yplus x) j) (U p) := by
        intro j; simp only [mulVec, dotProduct, Fin.sum_univ_two]
        have ha : ∀ a b, ContDiffOn ℝ ∞ (fun x => adjugate (X p x) a b) (U p) := by
          intro a b
          have heq : Set.EqOn (fun z => adjugate (X p z) a b)
              (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ a b) (U p) := fun z hz => adj_X_entry_eq p hz a b
          exact (contDiffOn_const.mul ((contDiffOn_Xinv_entry p a b).of_le le_top)).congr (fun z hz => heq hz)
        exact ((ha j 0).mul (hyp 0)).add ((ha j 1).mul (hyp 1))
      have hzm : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => ((X p x)ᴴ *ᵥ yminus x) j) (U p) :=
        fun j => contDiffOn_Xstar_mulVec p hym j
      have r1 := system4_yplus_of_system7 p (fun z => adjugate (X p z) *ᵥ yplus z) (fun z => (X p z)ᴴ *ᵥ yminus z) sg om mm hzp hx h1
      have r2 := system4_yminus_of_system7 p (fun z => adjugate (X p z) *ᵥ yplus z) (fun z => (X p z)ᴴ *ᵥ yminus z) sg om mm hzm hx h2
      -- round trips: k⁻¹ X adj(X) y+ = y+ on U ; (X^H)⁻¹ X^H y- = y- on U
      have hrt1 : Set.EqOn (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ (adjugate (X p z) *ᵥ yplus z))) yplus (U p) := by
        intro z hz; simp only
        rw [mulVec_mulVec, mul_adjugate, det_X p hz, smul_mulVec, one_mulVec, smul_smul,
          inv_mul_cancel₀ (by exact_mod_cast Q_sq_sub_M_sq_ne_zero p), one_smul]
      have hrt2 : Set.EqOn (fun z => ((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ yminus z)) yminus (U p) := by
        intro z hz; simp only; rw [mulVec_mulVec, inv_mul_Xstar p hz, one_mulVec]
      have e1 : ∀ j, Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ (adjugate (X p z) *ᵥ yplus z))) j) x
          = Dm p (fun z => yplus z j) x := fun j => Dm_congr p hx (fun z hz => congr_fun (hrt1 hz) j)
      have e2 : ∀ j, Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ yminus z)) j) x
          = Dp p (fun z => yminus z j) x := fun j => Dp_congr p hx (fun z hz => congr_fun (hrt2 hz) j)
      simp only [e1, e2, hrt1 hx, hrt2 hx] at r1 r2
      exact ⟨r1, r2⟩

end
