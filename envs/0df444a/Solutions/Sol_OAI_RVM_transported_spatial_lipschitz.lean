-- Prove2me | solution 1 for OAI.RVM.transported_spatial_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:46:25.906026+00:00
-- url     : https://prove2.me/submissions/bdfed26f-48d5-4a51-b367-806b884ade2f

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_transported_comparison

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma transported_spatial_lipschitz_oai {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A L N : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s.f (t,z')|≤(A*Real.exp ((1+2*N+L)*T))*‖z-z'‖ := by
  have hh := transported_comparison hs.smooth_f hs.smooth_f hE hB hE hB hV hV
    hs.initial_f hs.initial_f hA hL hN (D:=0) le_rfl ha hBb hEx hBx
      (by intros; simp) (by intros; simp) ht z z'
  simp only [mul_zero,zero_mul,add_zero] at hh
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith : 0≤1+2*N+L))
  exact hh.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg hA (norm_nonneg _))).trans_eq (by ring))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.transported_spatial_lipschitz_oai := @OAI.RVM.transported_spatial_lipschitz_oai
