-- Prove2me | solution 1 for Hintz2026.system7_zplus_of_system4
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:00:13.721803+00:00
-- url     : https://prove2.me/submissions/82bdcd38-e91b-4a26-819b-e3ac680ce909

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Dm_adj_matrix
import Theorems.Thm_Hintz2026_Cmat_mul_Xstar

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026
-- inlined helpers (local source: Atlas/Perturbations/Hintz2026/*.lean at 8d059e0)
variable (p : SubextremalKN)

theorem hadj_of_smooth {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => adjugate (X p (update x k u)) i j) (x k) := by
  have heq : Set.EqOn (fun z => adjugate (X p z) i j)
      (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    fun z hz => adj_X_entry_eq p hz i j
  have hsm : ContDiffOn ℝ ∞ (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    contDiffOn_const.mul ((contDiffOn_Xinv_entry p i j).of_le le_top)
  have hsm' : ContDiffOn ℝ ∞ (fun z => adjugate (X p z) i j) (U p) :=
    hsm.congr (fun z hz => heq hz)
  exact differentiableAt_slice p hsm' hx k

theorem Dm_adj_mulVec {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (y : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (hy : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => y x j) (U p)) :
    (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ y z) i) x) =
    -(adjugate (X p x) * A p x) *ᵥ y x + adjugate (X p x) *ᵥ (fun j => Dm p (fun z => y z j) x) := by
  ext i
  rw [Dm_mulVec_entry p (fun z => adjugate (X p z)) y x i
    (fun j k => hadj_of_smooth p hx i j k) (fun j k => hv_of_smooth p hy hx j k)]
  rw [Dm_adj_matrix p hx]
  rfl

end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h4 : (fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x) : (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ zminus p yminus x :=
  by
    rw [Dm_adj_mulVec p hx yplus hyp]
    -- Dm y+ = A y+ + (cI-B) y-
    have hDm : (fun j => Dm p (fun z => yplus z j) x) =
        A p x *ᵥ yplus x + (cscalar p sg om mm x • 1 - Bmat p sg om mm x) *ᵥ yminus x := by
      rw [← h4]; abel
    rw [hDm, mulVec_add, mulVec_mulVec, mulVec_mulVec, neg_mulVec]
    simp only [neg_add_cancel_left]
    unfold zminus
    rw [mulVec_mulVec, Cmat_mul_Xstar p sg om mm hx]

end
